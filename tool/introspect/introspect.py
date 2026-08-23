#!/usr/bin/env python3
# Copyright 2026 Vitaly Reznik
# SPDX-License-Identifier: Apache-2.0
"""introspect — тетрадь: разложение КОДА на атомы с метками ZTL. БЕЗ КЛЮЧА.

    ./introspect.py prepare  <файл-или-папка> [--out DIR]
    ./introspect.py assemble <папка-вердиктов> [--out ledger.md]

Тетрадь применяет метки оси ценности ТЕЛА (zchoose.VALUE_MARKS: T/T?/S) к коду плюс
проверочные F/Z/E: для каждого .py размечается СТАТУС элементарных claim'ов и
допущений, на которых код держится. Это разметка статуса проверки, не поиск багов.

СУДЬЯ — НЕ КЛЮЧ, А ФОРК ИЛИ Я САМ (решение куратора 2026-08-23). Раньше тетрадь
ходила по API-ключу Anthropic и жгла деньги. Теперь она НЕ зовёт API: `prepare`
пишет по task'у на файл (рубрика + код), а судит их либо ФОРК (субагент — как линза),
либо Я САМ в контексте (для одного мелкого файла форк — лишнее). `assemble` сшивает
вердикты в credit-ledger. Оба — по бюджету сессии, ключ не тронут.

ТЕТРАДЬ НА ТЕЛЕ: метки оси ценности (T/T?/S) берутся из zchoose.VALUE_MARKS — одно
определение на две руки. Улучшил тело — улучшил тетрадь.
"""
from __future__ import annotations

import argparse
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import zchoose                             # noqa: E402 — ТЕЛО яруса 3 (источник меток)

# ТЕТРАДЬ НА ТЕЛЕ. Метки оси ценности (T/T?/S) из тела zchoose.VALUE_MARKS —
# одно определение на две руки, а не два. Тетрадь — рука; улучшил тело — улучшил тетрадь.
PROMPT = """Разложи этот код на АТОМАРНЫЕ утверждения — элементарные claim'ы и \
допущения, на которых он держится (что каждая функция ожидает от входа, что \
гарантирует на выходе, какие инварианты предполагает про состояние и внешние данные).

Каждому атому поставь метку. Метки оси ЦЕННОСТИ (из тела яруса 3):
""" + zchoose.VALUE_MARKS + """

Плюс проверочные:
- F = утверждается, но ЛОЖНО;
- Z = взято в КРЕДИТ — допущение, которое код НЕ проверяет;
- E = судить не на чем.

Не ищи баги специально и не делай code review — честно размечай СТАТУС каждого атома.

Верни ТОЛЬКО действенные атомы (Z, F, S, T?), компактно, по одному на строку:
    - [MARK] функция:строка — formulation (краткая заметка; для T?/S — во что оборачивается)
В самом конце ОДНОЙ строкой: `T=<число> E=<число>` (сколько атомов вышло T и E).

Файл: {name}

```python
{code}
```"""


def py_files(target: pathlib.Path) -> list[pathlib.Path]:
    if target.is_file():
        return [target]
    out = [p for p in sorted(target.rglob("*.py"))
           if not p.name.startswith("test_") and "__pycache__" not in p.parts]
    return out


def prepare(target: pathlib.Path, out_dir: pathlib.Path) -> list[pathlib.Path]:
    """По task'у на .py файл (рубрика + код). Судья — форк/я, НЕ ключ."""
    files = py_files(target)
    if not files:
        sys.exit("нет .py файлов для разбора")
    root = target if target.is_dir() else target.parent
    out_dir.mkdir(parents=True, exist_ok=True)
    tasks = []
    for i, path in enumerate(files, 1):
        rel = path.relative_to(root) if (root in path.parents or root == path.parent) else path.name
        code = path.read_text(encoding="utf-8", errors="replace")
        body = f"<!-- task {i:02d} — {rel} -->\n\n" + PROMPT.format(name=str(rel), code=code)
        p = out_dir / f"task-{i:02d}.md"
        p.write_text(body, encoding="utf-8")
        tasks.append(p)
    n = len(tasks)
    print(f"подготовлено {n} task'ов в {out_dir}", file=sys.stderr)
    if n == 1:
        print("  → 1 файл: СУДИ САМ в своём контексте (форк ради одного файла — лишнее).",
              file=sys.stderr)
    else:
        print(f"  → {n} файлов: раздай ФОРКАМ (по субагенту на task) или суди подряд сам;",
              file=sys.stderr)
        print("    каждый вердикт в verdicts/verdict-NN.md, потом `assemble verdicts/`.",
              file=sys.stderr)
    return tasks


def assemble(verdicts_dir: pathlib.Path, out: pathlib.Path, source_name: str = "") -> pathlib.Path:
    """Сшить вердикты форков/мои в единый credit-ledger (судья — форк/я, без ключа)."""
    files = sorted(verdicts_dir.glob("verdict-*.md"))
    if not files:
        sys.exit(f"нет вердиктов в {verdicts_dir} (ждём verdict-NN.md)")
    body = "\n\n".join(f.read_text(encoding="utf-8").strip() for f in files)
    counts = {}
    for ln in body.splitlines():                 # метки только на строках-атомах (буллет)
        if re.match(r"\s*[-*]\s", ln):
            for m in re.findall(r"\[(T\?|S|T|F|Z|E)\]", ln):
                counts[m] = counts.get(m, 0) + 1
    head = [f"# credit-ledger — {source_name or verdicts_dir.name}", "",
            "Тетрадь на теле (introspect), судья — ФОРК/сам (без ключа). "
            "Метки: T проверено / T? уязвимое / S соблазн / F ложь / Z кредит / E не на чем.",
            f"Кусков: {len(files)}. Сводка меток: "
            + ("  ".join(f"{k}={v}" for k, v in sorted(counts.items())) or "—") + ".",
            "", "---", ""]
    out.write_text("\n".join(head) + body + "\n", encoding="utf-8")
    print(f"ledger -> {out}  (кусков {len(files)}, метки { {k: counts[k] for k in counts} })",
          file=sys.stderr)
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description="тетрадь БЕЗ КЛЮЧА: подготовить код для форка/себя, сшить ledger")
    sub = ap.add_subparsers(dest="cmd", required=True)

    pp = sub.add_parser("prepare", help="по task'у на .py файл (рубрика+код), судья — форк/я")
    pp.add_argument("target", help="файл .py или папка проекта")
    pp.add_argument("--out", default=None, help="куда класть task'и (по умолч. <цель>.tasks/)")

    pa = sub.add_parser("assemble", help="сшить вердикты форков/мои в credit-ledger")
    pa.add_argument("verdicts", help="папка с verdict-NN.md")
    pa.add_argument("--out", default=None, help="куда писать ledger")

    args = ap.parse_args()

    if args.cmd == "prepare":
        target = pathlib.Path(args.target).resolve()
        if not target.exists():
            sys.exit(f"нет такого пути: {target}")
        out_dir = pathlib.Path(args.out) if args.out else pathlib.Path(str(target) + ".tasks")
        prepare(target, out_dir)
        return 0

    if args.cmd == "assemble":
        vdir = pathlib.Path(args.verdicts).resolve()
        out = pathlib.Path(args.out) if args.out else (vdir.parent / f"credit-ledger-{vdir.parent.name}.md")
        assemble(vdir, out)
        return 0

    return 0


if __name__ == "__main__":
    sys.exit(main())
