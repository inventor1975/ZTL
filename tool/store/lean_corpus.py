#!/usr/bin/env python3
"""Корпус Lean для атом-стора — БЕЗ ФОРКОВ И БЕЗ ТОКЕНОВ.

Замысел (куратор, 2026-08-25): Lean — не проза. Атом прозы надо ИЗВЛЕКАТЬ:
переформулировать, раскрыть местоимения — там нужен форк. А в Lean утверждение
уже записано формально и однозначно: имя и формулировка не извлекаются, а
БЕРУТСЯ. Потому корпус собирается разбором исходников, за секунды и даром.

И он ВЕРНЕЕ форкового: пересказ теоремы приблизителен, взятая формулировка точна
до символа. МЕРЕНО: 340к слов нашего Lean форками стоили бы ~2,4 млн токенов;
машинно — 2 053 объекта за 0,13с.

Зачем: судья того, «как логика РАБОТАЕТ», — код, а не статья о коде. Числа теорем
и имена модулей путаются первыми ([[project_selfcheck_control_questions]]).

Единица несёт `"kind": "lean"` — не путать с извлечённым атомом прозы.
"""
from __future__ import annotations
import argparse
import json
import pathlib
import re
import sys

DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(theorem|lemma|def|instance|abbrev|structure)\s+"
                  r"([A-Za-z_0-9'.«»]+)(.*)$")
AXIOM_LINE = re.compile(r"#print\s+axioms\s+([A-Za-z_0-9'.]+)")
SKIP_PARTS = (".lake", "_attic", "build")
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent))
from atomstore import flag_injection  # noqa: E402


def declarations(root: pathlib.Path) -> list[dict]:
    """Взять объявления как они записаны. Формулировка — до `:=`, склеенная по
    строкам продолжения (в Lean она часто переносится)."""
    out = []
    for f in sorted(root.rglob("*.lean")):
        if any(s in str(f.relative_to(root)).split("/") for s in SKIP_PARTS):
            continue
        text = f.read_text(encoding="utf-8", errors="replace")
        audited = set(AXIOM_LINE.findall(text))     # у кого стоит #print axioms
        lines = text.splitlines()
        for i, line in enumerate(lines):
            m = DECL.match(line)
            if not m:
                continue
            kind, name, tail = m.group(1), m.group(2), m.group(3)
            stmt = tail
            j = i + 1
            # добираем перенос, пока не встретили `:=` или не кончилось объявление
            while ":=" not in stmt and j < len(lines) and j < i + 8:
                nxt = lines[j].strip()
                if not nxt or DECL.match(lines[j]):
                    break
                stmt += " " + nxt
                j += 1
            stmt = stmt.split(":=")[0].strip().strip(":").strip()
            stmt = " ".join(stmt.split())
            if not stmt:
                continue
            out.append({"kind_lean": kind, "name": name, "stmt": stmt,
                        "file": str(f), "line": i + 1,
                        "axioms_printed": name in audited})
    return out


def build(sources: list[tuple], corpus: str, store_root: pathlib.Path) -> int:
    total = 0
    for label, root in sources:
        decls = declarations(pathlib.Path(root))
        by_file: dict = {}
        for d in decls:
            rel = f"{label}/" + str(pathlib.Path(d["file"]).relative_to(root))
            audit = " [аксиомы проверены #print axioms]" if d["axioms_printed"] else ""
            unit = (f"{d['kind_lean']} {d['name']} : {d['stmt']}"
                    f"  ({rel}:{d['line']}){audit}")
            u = {"atom": unit, "src": rel, "chunk": d["line"], "kind": "lean"}
            if flag_injection(unit):
                u["suspect"] = "адресовано модели, не читателю"
            by_file.setdefault(rel, []).append(u)
        for rel, units in by_file.items():
            out = store_root / corpus / (rel + ".atoms.jsonl")
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text("\n".join(json.dumps(u, ensure_ascii=False) for u in units),
                           encoding="utf-8")
            total += len(units)
        print(f"  {label}: {len(decls)} объявлений из {len(by_file)} файлов")
    print(f"lean-corpus: {total} единиц (БЕЗ форков, 0 токенов) в {store_root/corpus}")
    return total


def main() -> int:
    ap = argparse.ArgumentParser(description="Корпус Lean для атом-стора, машинно")
    ap.add_argument("--store", default="atomstore")
    ap.add_argument("--corpus", default="LEAN")
    ap.add_argument("--source", action="append", required=True,
                    metavar="МЕТКА=ПУТЬ", help="например VR=/path/VRCycle (можно несколько)")
    a = ap.parse_args()
    srcs = [tuple(s.split("=", 1)) for s in a.source]
    build(srcs, a.corpus, pathlib.Path(a.store))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
