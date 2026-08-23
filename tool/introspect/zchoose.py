#!/usr/bin/env python3
# Copyright 2026 Vitaly Reznik
# SPDX-License-Identifier: Apache-2.0
"""zchoose — ТЕЛО яруса 3: выбиратель доброго среди истинного. БЕЗ КЛЮЧА.

    ./zchoose.py prepare  <текст-файл> [--out DIR] [--target N]
    ./zchoose.py assemble <папка-вердиктов> [--out ledger.md]

Ярус 3 (этика/выбор). Ниже: проверка (ztl.py — T/F/Z) и суд (zboundary — E).
Сюда приходит уже ИСТИННОЕ. Вопрос не «истинно ли», а «истинное — ДОБРОЕ ли,
или СОБЛАЗН (истинно, но во вред)». Задача — выбрать доброе, отбросить соблазн.

СУДЬЯ — НЕ КЛЮЧ, А ФОРК ИЛИ Я САМ (решение куратора 2026-08-23). Раньше тело
ходило по API-ключу Anthropic и жгло деньги орга. Теперь тело НЕ зовёт API вовсе:
оно РЕЖЕТ текст по швам и готовит task'и (рубрика + кусок), а судит их либо ФОРК
(субагент в сессии — как линза, только вместо «найди баги» задача «размерь атомы»),
либо Я САМ в своём контексте (для малого — ради абзаца форк не нужен). Оба — по
бюджету сессии, ключ не тронут.

ЧЕСТНАЯ ГРАНИЦА. Соблазн НЕ вычислим из частей: вред живёт в УПОТРЕБЛЕНИИ, не в
утверждении — та же причина, по которой S не пускают в ядро (сломало бы truth-
functionality). Потому тело — НЕ алгоритм, а КОДИФИЦИРОВАННАЯ ПРОЦЕДУРА СУЖДЕНИЯ:
одна алгоритмическая зацепка (тэлл абсолюта) НАВОДИТ, вердикт даёт судья по рубрике.

ТРИ МЕТКИ ОСИ ЦЕННОСТИ (промерены обкаткой на границе, «О помощи», 2026-08-23):
    T   доброе — истинно и стоит само, не во вред.
    T?  T-УЯЗВИМОЕ — доброе КАК СКАЗАНО, но легко оборачивается во вред при иной
        рамке («сначала обеспечь себя»: мудрость ИЛИ вечное себя-вперёд).
    S   СОБЛАЗН — истинное зерно УЖЕ обёрнуто в оправдание холода/расчёта/сдачи
        («не спасёшь, сколько ни вкладывай»): нож уже повёрнут.

Различие T? и S — в РАМКЕ: обёрнуто ли УЖЕ, или лишь оборачиваемо. И соблазн часто
ЕДЕТ НА АБСОЛЮТЕ («всякий/никогда/сколько ни»): размашистость оборачивает правду в
яд, потому абсолют — тэлл, где искать. Дисциплина: не мазать доброе в S из паранойи
и не пропускать тонкий яд.
"""
from __future__ import annotations

import argparse
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent

# Тэлл абсолюта — единственная АЛГОРИТМИЧЕСКАЯ зацепка тела: наводит на места, где
# правда чаще всего оборачивается в яд. Это не вердикт, а «смотри сюда»: соблазн
# может быть и без абсолюта (тогда его берёт судья), и абсолют бывает невинным.
# Матчим по ГРАНИЦЕ СЛОВА, иначе «всё же» ложно ловится в «все», а «всех разумных»
# шумит — оставлены только ясные квантор-абсолюты, дискурсивное «всё же» убрано.
ABSOLUTES = [
    r"всяк\w*", r"кажд\w*", r"люб(ой|ому|ого|ая|ые)", r"никто", r"никого",
    r"никому", r"никогда", r"всегда", r"вечно", r"сколько ни", r"ни один\w*",
    r"ни одного", r"только тем\b", r"только те\b", r"лишь те\w*", r"во что бы",
]
_ABS_RE = re.compile(r"(?<!\w)(" + "|".join(ABSOLUTES) + r")(?!\w)")


def absolute_flags(text: str) -> list[str]:
    """Куски текста, несущие абсолют — где искать соблазн (тэлл, не вердикт)."""
    low = text.lower().replace("ё", "е")
    hits = []
    for m in _ABS_RE.finditer(low):
        s = max(0, m.start() - 24)
        e = min(len(text), m.end() + 30)
        hits.append(f"…{text[s:e].strip()}…  [абсолют: {m.group(1)}]")
    return hits


# Канонические метки оси ЦЕННОСТИ (ярус 3). Их ИМПОРТИРУЕТ тетрадь (introspect),
# чтобы S/T? были ОДНИМ определением на две руки, а не двумя. Тело — источник,
# тетрадь — рука. В коде и в рассуждении S = одно «истинно, но во вред», примеры разные.
VALUE_MARKS = """- T  = ДОБРОЕ: истинно и стоит само, не во вред.
- T? = T-УЯЗВИМОЕ: истинно и доброе КАК СКАЗАНО (в коде — инвариант держится СЕЙЧАС), \
но легко оборачивается во вред при иной рамке/входе. Скажи, во что оборачивается.
- S  = СОБЛАЗН (Seduction): истинное зерно УЖЕ обёрнуто во вред. В коде — утечка, рост \
без предела, инвариант, что не роняет, но копит вред. В рассуждении — истина, \
употреблённая для оправдания холода, расчёта, инструментализации, сдачи. Нож уже повёрнут."""

RUBRIC = """Ты — ярус ЭТИКИ/ВЫБОРА над логикой проверки. Тебе дают РАССУЖДЕНИЕ, в \
котором ходы УЖЕ считаются истинными. Твой вопрос не «истинно ли», а «истинное — \
ДОБРОЕ ли, или соблазн». Разложи текст на атомарные ходы и каждому поставь метку:

""" + VALUE_MARKS + """
- F  = ложь (опровержимо контрпримером). Z = размашистый абсолют на веру. E = судить не на чем.

КЛЮЧ РАЗЛИЧЕНИЯ T? и S — РАМКА: T? лишь ОБОРАЧИВАЕМО, S УЖЕ обёрнуто в этом тексте. \
Соблазн часто ЕДЕТ НА АБСОЛЮТЕ («всякий/никогда/сколько ни») — размашистость и есть \
обёртка. Дисциплина: НЕ мазать доброе в S из паранойи; НЕ пропускать тонкий яд.
ВАЖНО — УПОТРЕБЛЕНИЕ, НЕ УПОМИНАНИЕ: если текст ЦИТИРУЕТ соблазн/ложь как ход \
оппонента и тут же ОПРОВЕРГАЕТ — это НЕ дефект текста; помечай статус САМОГО текста, \
а не процитированного ножа.

Верни каждый ход: цитата (кратко) — [МЕТКА] — одна строка почему (для T?/S — в чём \
оборачивание/рамка). В конце — раздел ВЫБОР: какие ходы ОСТАВить (T, и T? с явным \
предупреждением рамки), какие ОТБРОСИТЬ (S), одной фразой — что выбрать по совести, \
а не «просто логично».

Текст:

{text}"""


# ЧАНКИНГ — промерен 2026-08-23 (см. память project_atom_notebook_experiment). Целый
# длинный текст судье не по зубам за раз; чанки — способ досчитать. Режем по
# ЕСТЕСТВЕННЫМ швам (заголовки/границы абзацев), НИКОГДА не поперёк абзаца: на
# ценностной оси рамка И ЕСТЬ суждение, и край куска пере-обрамляет пограничные T?/T.
def chunk_prose(text: str, target_lines: int = 50) -> list[tuple[str, str]]:
    """Резать прозу по швам: копим абзацы до target_lines непустых строк, заголовок
    верхнего уровня (# …) открывает новый чанк. Возвращает [(метка-зачин, текст)]."""
    paras = [p for p in text.split("\n\n") if p.strip()]
    chunks: list[str] = []
    cur: list[str] = []
    cnt = 0
    for p in paras:
        stripped = p.lstrip()
        is_top = stripped.startswith("# ") or stripped.rstrip() == "#"
        if is_top and cur:
            chunks.append("\n\n".join(cur)); cur, cnt = [], 0
        cur.append(p); cnt += p.count("\n") + 1
        if cnt >= target_lines and not is_top:
            chunks.append("\n\n".join(cur)); cur, cnt = [], 0
    if cur:
        chunks.append("\n\n".join(cur))
    out = []
    for c in chunks:
        first = next((ln.strip() for ln in c.splitlines() if ln.strip()), "")
        out.append((first[:60], c))
    return out


def prepare(text: str, out_dir: pathlib.Path, target_lines: int = 50) -> list[pathlib.Path]:
    """Нарезать текст и написать по task'у на кусок (рубрика+кусок). Судья — форк/я,
    НЕ ключ. Возвращает пути task'ов; печатает тэлл и как потреблять (форк/сам)."""
    chunks = chunk_prose(text, target_lines)
    out_dir.mkdir(parents=True, exist_ok=True)
    tasks = []
    for i, (label, ctext) in enumerate(chunks, 1):
        tell = absolute_flags(ctext)
        tell_block = ""
        if tell:
            tell_block = ("\n\n<!-- ТЭЛЛ АБСОЛЮТА (наводка, не вердикт):\n"
                          + "\n".join(f"  {t}" for t in tell) + "\n-->")
        body = f"<!-- task {i:02d} — {label} -->\n\n" + RUBRIC.format(text=ctext) + tell_block
        p = out_dir / f"task-{i:02d}.md"
        p.write_text(body, encoding="utf-8")
        tasks.append(p)
    n = len(tasks)
    print(f"подготовлено {n} task'ов в {out_dir}", file=sys.stderr)
    if n == 1:
        print("  → 1 кусок: СУДИ САМ в своём контексте (форк ради абзаца — лишнее).",
              file=sys.stderr)
    else:
        print(f"  → {n} кусков: раздай ФОРКАМ (по субагенту на task, параллельно) или суди подряд сам;",
              file=sys.stderr)
        print("    каждый вердикт положи в verdicts/verdict-NN.md, потом `assemble verdicts/`.",
              file=sys.stderr)
    return tasks


def assemble(verdicts_dir: pathlib.Path, out: pathlib.Path, source_name: str = "") -> pathlib.Path:
    """Сшить вердикты (verdict-NN.md, судья — форк/я) в единый credit-ledger."""
    files = sorted(verdicts_dir.glob("verdict-*.md"))
    if not files:
        sys.exit(f"нет вердиктов в {verdicts_dir} (ждём verdict-NN.md)")
    body = "\n\n".join(f.read_text(encoding="utf-8").strip() for f in files)
    # Считаем метки ТОЛЬКО на строках-атомах (буллет «- …»), не в прозе ВЫБОРа —
    # иначе повтор метки в выборе задваивает счёт (S=2 атома читались как 4).
    counts = {}
    for ln in body.splitlines():
        if re.match(r"\s*[-*]\s", ln):
            for m in re.findall(r"\[(T\?|S|T|F|Z|E)\]", ln):
                counts[m] = counts.get(m, 0) + 1
    head = [f"# credit-ledger — {source_name or verdicts_dir.name}", "",
            "Ярус 3 (zchoose), судья — ФОРК/сам (без ключа). "
            "Метки: T доброе / T? уязвимое / S соблазн / F ложь / Z кредит / E не на чем.",
            f"Кусков: {len(files)}. Сводка меток: "
            + ("  ".join(f"{k}={v}" for k, v in sorted(counts.items())) or "—") + ".",
            "", "---", ""]
    out.write_text("\n".join(head) + body + "\n", encoding="utf-8")
    print(f"ledger -> {out}  (кусков {len(files)}, метки { {k: counts[k] for k in counts} })",
          file=sys.stderr)
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description="ярус 3 БЕЗ КЛЮЧА: подготовить куски для форка/себя, сшить ledger")
    sub = ap.add_subparsers(dest="cmd", required=True)

    pp = sub.add_parser("prepare", help="нарезать текст на task'и (рубрика+кусок), судья — форк/я")
    pp.add_argument("target", help="текст-файл рассуждения")
    pp.add_argument("--out", default=None, help="куда класть task'и (по умолч. <файл>.tasks/)")
    pp.add_argument("--lines", type=int, default=50, dest="target_lines",
                    help="целевой размер куска в строках")

    pa = sub.add_parser("assemble", help="сшить вердикты форков/мои в credit-ledger")
    pa.add_argument("verdicts", help="папка с verdict-NN.md")
    pa.add_argument("--out", default=None, help="куда писать ledger")

    args = ap.parse_args()

    if args.cmd == "prepare":
        target = pathlib.Path(args.target).resolve()
        text = target.read_text(encoding="utf-8", errors="replace")
        out_dir = pathlib.Path(args.out) if args.out else target.with_suffix(target.suffix + ".tasks")
        prepare(text, out_dir, args.target_lines)
        return 0

    if args.cmd == "assemble":
        vdir = pathlib.Path(args.verdicts).resolve()
        out = pathlib.Path(args.out) if args.out else (vdir.parent / f"credit-ledger-{vdir.parent.name}.md")
        assemble(vdir, out)
        return 0

    return 0


if __name__ == "__main__":
    sys.exit(main())
