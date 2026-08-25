#!/usr/bin/env python3
"""Рабочий журнал ассистента — чтобы «что было» можно было СПРОСИТЬ, а не вспоминать.

Замысел куратора 2026-08-25: «есть проблема с временной памятью — постоянно новое,
что-то уходит, что-то приходит. А вот атомстор если применить: файлик,
атомизировать каждый раз, с лимитом по размеру, чтобы не дорого. И ты всегда
сможешь себя спросить.»

ЧТО ЭТО ЛЕЧИТ. Постоянная память хранит ДУРАБЕЛЬНОЕ: кто есть кто, правила, уроки.
Она не хранит ТЕКУЩЕЕ: что я час назад решил, что сейчас в работе, чего жду, что
уже отдал. Именно это и теряется при сжатии контекста и на границе сессий — и
теряется молча, потому что отсутствие записи неотличимо от «этого не было».

ЧЕГО ЭТО НЕ ДЕЛАЕТ. Журнал — запись МОИХ действий и решений, а не источник о мире.
Заземлять на него утверждения о фактах нельзя: это тот же круг, что с памятью
([[project_atomstore_grounded_corpus]]). Годится для «что я делал и что решил»,
не годится для «как оно устроено на самом деле».

Дёшево: запись — строка в файл; атомизация — режим --direct, ноль токенов;
индекс — секунды на GPU. Потолок держит файл в размере, старое уезжает в .1.
"""
from __future__ import annotations
import argparse
import datetime
import pathlib
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
DEFAULT = pathlib.Path.home() / ".claude" / "work-journal.md"
MAX_BYTES = 512 * 1024          # потолок: дальше поворот, чтобы не росло без предела


def add(text: str, kind: str = "ход", path: pathlib.Path = DEFAULT) -> None:
    """Дописать запись. kind: ход | решение | находка | отдано | жду."""
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists() and path.stat().st_size > MAX_BYTES:
        path.replace(path.with_suffix(path.suffix + ".1"))
        print(f"журнал повёрнут ({MAX_BYTES // 1024} КБ)", file=sys.stderr)
    stamp = datetime.datetime.now().astimezone().strftime("%Y-%m-%d %H:%M %Z")
    with path.open("a", encoding="utf-8") as f:
        f.write(f"\n## {stamp} — {kind}\n\n{text.strip()}\n")
    print(f"записано в журнал: {kind}, {len(text)} символов")


def index(path: pathlib.Path = DEFAULT, store: pathlib.Path = None) -> None:
    """Положить журнал в атом-стор корпусом JOURNAL — абзацами, БЕЗ форков."""
    if not path.exists():
        print("журнала ещё нет", file=sys.stderr); return
    src = path.parent / "_journal_src"
    src.mkdir(exist_ok=True)
    (src / path.name).write_text(path.read_text(encoding="utf-8"), encoding="utf-8")
    store = store or (pathlib.Path.cwd() / "atomstore")
    for args in (["atomize", "JOURNAL", str(src), "--store", str(store), "--direct"],
                 ["index", "JOURNAL", "--store", str(store), "--gpu", "--multilingual"]):
        r = subprocess.run([sys.executable, str(HERE / "atomstore.py"), *args],
                           capture_output=True, text=True)
        print("  " + (r.stdout.strip().splitlines() or ["(пусто)"])[-1])


def main() -> int:
    ap = argparse.ArgumentParser(description="Рабочий журнал: записать и спросить")
    sub = ap.add_subparsers(dest="cmd", required=True)
    pa = sub.add_parser("add"); pa.add_argument("text")
    pa.add_argument("--kind", default="ход",
                    choices=["ход", "решение", "находка", "отдано", "жду"])
    pi = sub.add_parser("index"); pi.add_argument("--store", default=None)
    a = ap.parse_args()
    if a.cmd == "add":
        add(a.text, a.kind)
    else:
        index(store=pathlib.Path(a.store) if a.store else None)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
