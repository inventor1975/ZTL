#!/usr/bin/env python3
# Copyright 2026 Vitaly Reznik
# SPDX-License-Identifier: Apache-2.0
"""introspect — разложение кода на АТОМЫ с метками ZTL, через Опуса.

    ./introspect.py <файл-или-папка> [--out ledger.md] [--model claude-opus-4-8]

Для каждого .py файла Опус размечает элементарные claim'ы и допущения, на
которых код держится, пятью метками:

    T  проверено ВЕРНО самим кодом (гарантирует на всех входах)
    F  утверждается, но ЛОЖНО
    Z  взято в КРЕДИТ — допущение, которое код НЕ проверяет
    E  судить не на чем
    S  «ДЫМ» — истинно, но ВРЕДНО (утечка, рост без предела, пропавший
       инвариант без падения): правдивое свойство, которое пахнет

Собирает единый credit-ledger: где проект берёт в кредит, где лжёт, где дымит.
Судья — Опус, не эвристика; это разметка СТАТУСА ПРОВЕРКИ, не поиск багов.

Ключ: env ANTHROPIC_API_KEY, иначе файл, указанный в --key / $INTROSPECT_KEYFILE,
иначе ./.anthropic_key рядом. Токены биллятся на этот ключ.
"""
from __future__ import annotations

import argparse
import concurrent.futures as cf
import os
import pathlib
import sys

import anthropic

HERE = pathlib.Path(__file__).resolve().parent
DEFAULT_MODEL = "claude-opus-4-8"        # промерено на нём; «Опус только» — слово куратора
MAX_TOKENS = 8000
CONCURRENCY = 6                          # файлов разом — как форки в сессии

PROMPT = """Разложи этот код на АТОМАРНЫЕ утверждения — элементарные claim'ы и \
допущения, на которых он держится (что каждая функция ожидает от входа, что \
гарантирует на выходе, какие инварианты предполагает про состояние и внешние данные).

Каждому атому поставь метку:
- T = проверено ВЕРНО самим кодом (гарантирует на всех входах);
- F = утверждается, но ЛОЖНО;
- Z = взято в КРЕДИТ — допущение, которое код НЕ проверяет;
- E = судить не на чем;
- S = «ДЫМ»: утверждение ИСТИННО, но ВРЕДНО — правдивое свойство кода, которое \
пахнет (утечка памяти, рост структуры без предела, пропавший инвариант, который \
не роняет, но копит вред). НЕ ложь и НЕ непроверенное допущение — верно, но нехорошо.

Не ищи баги специально и не делай code review — честно размечай СТАТУС каждого атома.

Верни ТОЛЬКО атомы с меткой Z, F или S (действенные), компактно, по одному на строку:
    [MARK] функция:строка — formulation (краткая заметка)
В самом конце ОДНОЙ строкой: `T=<число> E=<число>` (сколько атомов вышло T и E).

Файл: {name}

```python
{code}
```"""


def load_key(keyfile: str | None) -> str:
    k = os.environ.get("ANTHROPIC_API_KEY", "").strip()
    if k:
        return k
    for cand in (keyfile, os.environ.get("INTROSPECT_KEYFILE"), str(HERE / ".anthropic_key")):
        if cand and pathlib.Path(cand).is_file():
            return pathlib.Path(cand).read_text(encoding="utf-8").strip()
    sys.exit("нет ключа: задай ANTHROPIC_API_KEY, --key <файл> или положи .anthropic_key рядом")


def py_files(target: pathlib.Path) -> list[pathlib.Path]:
    if target.is_file():
        return [target]
    # весь проект .py, кроме тестов и служебного
    out = [p for p in sorted(target.rglob("*.py"))
           if not p.name.startswith("test_") and "__pycache__" not in p.parts]
    return out


def introspect_one(client: anthropic.Anthropic, model: str, path: pathlib.Path,
                   root: pathlib.Path) -> dict:
    rel = path.relative_to(root) if root in path.parents or root == path.parent else path.name
    code = path.read_text(encoding="utf-8", errors="replace")
    prompt = PROMPT.format(name=str(rel), code=code)
    try:
        # Стрим + adaptive thinking: разложение — сложное рассуждение, а поток
        # не даёт длинному ответу упереться в таймаут (см. Anthropic SDK).
        with client.messages.stream(
                model=model, max_tokens=MAX_TOKENS,
                thinking={"type": "adaptive"},
                messages=[{"role": "user", "content": prompt}]) as stream:
            msg = stream.get_final_message()
        text = "".join(b.text for b in msg.content if b.type == "text").strip()
        usage = msg.usage
        return {"file": str(rel), "text": text, "ok": True,
                "in_tok": usage.input_tokens, "out_tok": usage.output_tokens}
    except Exception as e:                 # один файл не должен ронять весь прогон
        return {"file": str(rel), "text": f"(ОШИБКА: {type(e).__name__}: {e})",
                "ok": False, "in_tok": 0, "out_tok": 0}


def main() -> int:
    ap = argparse.ArgumentParser(description="разложение кода на атомы (T/F/Z/E/S) через Опуса")
    ap.add_argument("target", help="файл .py или папка проекта")
    ap.add_argument("--out", default=None, help="куда писать ledger (по умолчанию рядом с целью)")
    ap.add_argument("--model", default=os.environ.get("INTROSPECT_MODEL", DEFAULT_MODEL))
    ap.add_argument("--key", default=None, help="файл с ключом (иначе env/.anthropic_key)")
    ap.add_argument("--jobs", type=int, default=CONCURRENCY, help="файлов разом")
    args = ap.parse_args()

    target = pathlib.Path(args.target).resolve()
    if not target.exists():
        sys.exit(f"нет такого пути: {target}")
    files = py_files(target)
    if not files:
        sys.exit("нет .py файлов для разбора")
    root = target if target.is_dir() else target.parent

    client = anthropic.Anthropic(api_key=load_key(args.key))
    print(f"introspect: {len(files)} файлов, модель {args.model}, по {args.jobs} разом…",
          file=sys.stderr)

    results = []
    with cf.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futs = {pool.submit(introspect_one, client, args.model, f, root): f for f in files}
        for fut in cf.as_completed(futs):
            r = fut.result()
            results.append(r)
            mark = "ok  " if r["ok"] else "СБОЙ"
            print(f"  {mark} {r['file']}  (+{r['out_tok']} tok)", file=sys.stderr)
    results.sort(key=lambda r: r["file"])

    in_tok = sum(r["in_tok"] for r in results)
    out_tok = sum(r["out_tok"] for r in results)
    lines = [f"# credit-ledger — {target.name}", "",
             f"Инструмент: introspect (Опус {args.model}), метки T/F/Z/E/S "
             f"(S = «дым»: истинно, но вредно).",
             f"Файлов: {len(files)}. Токены: вход {in_tok}, выход {out_tok} "
             f"(всего ~{(in_tok+out_tok)//1000}k).", ""]
    for r in results:
        lines += [f"## {r['file']}", "", "```", r["text"], "```", ""]
    ledger = "\n".join(lines)

    out = pathlib.Path(args.out) if args.out else (
        (target if target.is_dir() else target.parent) / f"credit-ledger-{target.stem}.md")
    out.write_text(ledger, encoding="utf-8")
    print(f"\nledger -> {out}  (~{(in_tok+out_tok)//1000}k токенов)", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
