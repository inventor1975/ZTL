#!/usr/bin/env python3
"""ZTL confabulation guard — БЕЗ КЛЮЧА.

Зеро-траст сверка ОТВЕТА против ИСТОЧНИКА: разложить ответ на атомы, каждому
метка T (форсит источник) / F (противоречит) / Z (не установлено). По умолчанию
Z — адверсариально к ответу. Наружу уходит только T; Z/F флагаются или ответ
переделывается вызывающим и гонится снова.

Как и introspect/zchoose — судья это ФОРК (субагент) или Я (SELF), не API-ключ.
Поток: prepare (источник+вопрос+ответ+рубрика -> task) -> суд -> assemble (леджер
+ заземлённый ответ).

Две опции источника (замысел куратора 2026-08-24):
  --mode roll      РУЛОН: весь источник в один контекст (когда влезает в окно).
  --mode chapters  ПО-ГЛАВАМ/файлам: форки многопоточно; атом = F если хоть один
                   кусок F; T если хоть один кусок T (и ни один не F); иначе Z.
"""
import argparse
import pathlib
import re
import sys

# chunk_prose живёт в zchoose — переиспользуем, не дублируем.
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from zchoose import chunk_prose  # noqa: E402

GROUNDING_RUBRIC = """Ты — ЗЕРО-ТРАСТ судья ОБОСНОВАННОСТИ. Тебе дают ИСТОЧНИК
(единственная истина), ВОПРОС и КАНДИДАТ-ОТВЕТ. Знание ВНЕ источника НЕ
использовать. Разложи ОТВЕТ на атомарные утверждения и каждому поставь метку:

- T = ФОРСИТ источник: текст утверждает это или строго влечёт.
- F = ПРОТИВОРЕЧИТ источнику.
- Z = НЕ УСТАНОВЛЕНО источником: текст молчит или не форсит. По умолчанию Z,
      когда текст не форсит ЯВНО — будь адверсариален к ответу, не давай истину
      в кредит. Вывод «A в тексте и B в тексте, значит C» — это Z для C, если C
      сам не форсится (истинные куски, кривая склейка = не обоснование).

Затем собери ЗАЗЕМЛЁННЫЙ ОТВЕТ: оставь только T; для Z/F либо выкинь, либо прямо
скажи «не установлено источником». Не протаскивай Z назад как вывод.

Верни РОВНО:
1) ЛЕДЖЕР — по строке на атом: «утверждение — [T|F|Z] — одна строка почему».
2) ЗАЗЕМЛЁННЫЙ ОТВЕТ — что уйдёт пользователю.
3) ВЕРДИКТ — одно: GROUNDED (все T) | REPAIRED (были Z/F, вычищено) |
   REFUSED (обосновать нечего)."""

_TASK = """<!-- guard task {idx} — mode={mode} -->

{rubric}

=== ИСТОЧНИК{scope} ===
{source}

=== ВОПРОС ===
{question}

=== КАНДИДАТ-ОТВЕТ (его и суди) ===
{answer}
"""

_MARK = re.compile(r"\[\s*(T|F|Z)\s*\]", re.I)


def prepare(source: str, question: str, answer: str, out_dir: pathlib.Path,
            mode: str = "roll", target_lines: int = 50) -> list[pathlib.Path]:
    """Нарезать task'и для судьи. roll = один кусок; chapters = по кускам."""
    out_dir.mkdir(parents=True, exist_ok=True)
    if mode == "roll":
        chunks = [("", source)]
    else:
        chunks = chunk_prose(source, target_lines=target_lines)
    written = []
    for i, (title, chunk) in enumerate(chunks, 1):
        scope = "" if mode == "roll" else f" (кусок {i}/{len(chunks)}: {title})"
        body = _TASK.format(idx=f"{i:02d}", mode=mode, rubric=GROUNDING_RUBRIC,
                            scope=scope, source=chunk, question=question,
                            answer=answer)
        p = out_dir / f"gtask-{i:02d}.md"
        p.write_text(body, encoding="utf-8")
        written.append(p)
    print(f"подготовлено {len(written)} task'ов (mode={mode}) в {out_dir}")
    print("  -> раздай ФОРКАМ (по субагенту на task) или суди сам; каждый вердикт")
    print("     в verdicts/verdict-NN.md (с ЛЕДЖЕРОМ строками «... — [T|F|Z] — ...»),")
    print("     потом `guard.py assemble verdicts/`.")
    return written


def _merge_mark(marks: list[str]) -> str:
    """Слить метку атома по кускам: F доминирует, потом T, иначе Z."""
    if "F" in marks:
        return "F"
    if "T" in marks:
        return "T"
    return "Z"


def assemble(verdicts_dir: pathlib.Path, out: pathlib.Path) -> pathlib.Path:
    """Сшить вердикты: по кускам слить метки, дать сводку и общий вердикт."""
    atoms: dict[str, list[str]] = {}
    for f in sorted(verdicts_dir.glob("*.md")):
        for line in f.read_text(encoding="utf-8").splitlines():
            m = _MARK.search(line)
            if not m:
                continue
            claim = line.split(m.group(0))[0].strip(" -–—•\t").strip()
            if claim:
                atoms.setdefault(claim, []).append(m.group(1).upper())
    merged = {c: _merge_mark(ms) for c, ms in atoms.items()}
    counts = {"T": 0, "F": 0, "Z": 0}
    for v in merged.values():
        counts[v] = counts.get(v, 0) + 1
    if counts["F"] == 0 and counts["Z"] == 0 and counts["T"] > 0:
        verdict = "GROUNDED"
    elif counts["T"] > 0:
        verdict = "REPAIRED"
    else:
        verdict = "REFUSED"
    lines = [f"# guard-ledger  (атомов {len(merged)}, {counts}, ВЕРДИКТ: {verdict})",
             "", "Метка атома слита по кускам: F доминирует, потом T, иначе Z.", ""]
    for c, v in sorted(merged.items(), key=lambda kv: "TFZ".index(kv[1]) if kv[1] in "TFZ" else 9):
        lines.append(f"- [{v}] {c}")
    lines += ["", "НАРУЖУ: оставить только [T]. [Z]/[F] — «не установлено источником» или выкинуть."]
    out.write_text("\n".join(lines), encoding="utf-8")
    print(f"ledger -> {out}  (атомов {len(merged)}, {counts}, ВЕРДИКТ: {verdict})")
    return out


def main() -> int:
    ap = argparse.ArgumentParser(
        description="ZTL confabulation guard БЕЗ КЛЮЧА: сверить ответ против источника (T/F/Z)")
    sub = ap.add_subparsers(dest="cmd", required=True)
    pp = sub.add_parser("prepare", help="нарезать task'и (источник+вопрос+ответ+рубрика)")
    pp.add_argument("source", help="файл-источник (истина)")
    pp.add_argument("--question", required=True)
    pp.add_argument("--answer", required=True, help="ответ для сверки (строка или @файл)")
    pp.add_argument("--mode", choices=["roll", "chapters"], default="roll")
    pp.add_argument("--out", default=None)
    pp.add_argument("--lines", type=int, default=50)
    pa = sub.add_parser("assemble", help="сшить вердикты в guard-ledger")
    pa.add_argument("verdicts", help="папка с вердиктами судьи")
    pa.add_argument("--out", default=None)
    a = ap.parse_args()
    if a.cmd == "prepare":
        src = pathlib.Path(a.source)
        source = src.read_text(encoding="utf-8")
        answer = (pathlib.Path(a.answer[1:]).read_text(encoding="utf-8")
                  if a.answer.startswith("@") else a.answer)
        out = pathlib.Path(a.out) if a.out else src.with_suffix(src.suffix + ".guard.tasks")
        prepare(source, a.question, answer, out, mode=a.mode, target_lines=a.lines)
    elif a.cmd == "assemble":
        vd = pathlib.Path(a.verdicts)
        out = pathlib.Path(a.out) if a.out else vd.parent / "guard-ledger.md"
        assemble(vd, out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
