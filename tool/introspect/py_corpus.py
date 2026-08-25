#!/usr/bin/env python3
"""Корпус Python для атом-стора — машинно, БЕЗ ФОРКОВ И ТОКЕНОВ.

ВАЖНАЯ РАЗНИЦА С LEAN, из-за неё срез узкий и с биркой. Теорему в Lean проверяет
компилятор: взял формулировку — взял проверенный факт. Докстроку в Python не
проверяет НИКТО: она говорит, что автор хотел сказать. Код меняется, докстрока
остаётся — и стор начнёт уверенно повторять неправду со ссылкой на файл и строку.
Ложь с адресом убедительнее лжи без адреса, потому такие единицы несут
`"kind": "py-doc"` и читать их надо как «код о себе говорит», НЕ как истину.

Что берём:
  1) докстрока модуля — что файл о себе заявляет;
  2) подпись функции/класса + первая строка её докстроки;
  3) строки с пометкой МЕРЕНО / MEASURED / промерено — ради них всё и затевалось:
     это числа, которые мы однажды промеряли, чтобы не перемерять вслепую, а
     память врёт про числа первой.

Судья ПОВЕДЕНИЯ кода — запущенный код, не этот корпус. Про таблицы ZTL спрашивают
ztl.py, а не докстроку о нём.
"""
from __future__ import annotations
import argparse
import ast
import json
import pathlib
import re
import sys

MEASURED = re.compile(r"(МЕРЕНО|ИЗМЕРЕНО|ПРОМЕРЕНО|MEASURED|промерено|мерено)", re.I)
SKIP = ("venv", ".venv", "site-packages", "__pycache__", ".lake", "node_modules")
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from atomstore import flag_injection  # noqa: E402


def units_of(path: pathlib.Path, rel: str) -> list[dict]:
    src = path.read_text(encoding="utf-8", errors="replace")
    out = []
    try:
        tree = ast.parse(src)
    except SyntaxError:
        return out
    mod_doc = ast.get_docstring(tree)
    if mod_doc:
        first = " ".join(mod_doc.strip().splitlines()[0:2]).strip()
        if len(first) > 15:
            u = {"atom": f"модуль {rel}: {first}", "src": rel, "chunk": 1,
                 "kind": "py-doc"}
            if flag_injection(first):
                u["suspect"] = "адресовано модели, не читателю"
            out.append(u)
    for node in ast.walk(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            continue
        kind = "class" if isinstance(node, ast.ClassDef) else "def"
        try:
            sig = ast.unparse(node.args) if hasattr(node, "args") else ""
        except Exception:
            sig = ""
        doc = ast.get_docstring(node) or ""
        first = doc.strip().splitlines()[0].strip() if doc else ""
        text = f"{kind} {node.name}({sig})" + (f" — {first}" if first else "")
        u = {"atom": f"{text}  ({rel}:{node.lineno})", "src": rel,
             "chunk": node.lineno, "kind": "py-doc"}
        if flag_injection(text):
            u["suspect"] = "адресовано модели, не читателю"
        out.append(u)
    # МЕРЕНЫЕ строки — отдельной породой, они и есть цель
    for i, line in enumerate(src.splitlines(), 1):
        s = line.strip()
        if MEASURED.search(s) and len(s) > 25:
            out.append({"atom": f"[МЕРЕНО] {s.lstrip('#').strip()}  ({rel}:{i})",
                        "src": rel, "chunk": i, "kind": "py-measured"})
    return out


def build(sources: list[tuple], corpus: str, store_root: pathlib.Path) -> int:
    total = meas = 0
    for label, root in sources:
        root = pathlib.Path(root)
        per_file: dict = {}
        for f in sorted(root.rglob("*.py")):
            if any(s in str(f.relative_to(root)).split("/") for s in SKIP):
                continue
            rel = f"{label}/" + str(f.relative_to(root))
            us = units_of(f, rel)
            if us:
                per_file[rel] = us
        for rel, us in per_file.items():
            out = store_root / corpus / (rel + ".atoms.jsonl")
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text("\n".join(json.dumps(u, ensure_ascii=False) for u in us),
                           encoding="utf-8")
            total += len(us)
            meas += sum(1 for u in us if u["kind"] == "py-measured")
        print(f"  {label}: {len(per_file)} файлов")
    print(f"py-corpus: {total} единиц, из них МЕРЕНЫХ {meas} "
          f"(БЕЗ форков, 0 токенов) в {store_root/corpus}")
    return total


def main() -> int:
    ap = argparse.ArgumentParser(description="Корпус Python для атом-стора, машинно")
    ap.add_argument("--store", default="atomstore")
    ap.add_argument("--corpus", default="PY")
    ap.add_argument("--source", action="append", required=True, metavar="МЕТКА=ПУТЬ")
    a = ap.parse_args()
    build([tuple(s.split("=", 1)) for s in a.source], a.corpus, pathlib.Path(a.store))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
