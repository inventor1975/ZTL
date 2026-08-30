# -*- coding: utf-8 -*-
"""Стенд на правило куратора 2026-08-30: «атом стор не разбиваем форком отныне».

Правило легко откатить случайно — достаточно кому-то поправить умолчание флага.
Поэтому оно проверяется КОДОМ, а не памятью.

Проверяем три вещи, и третья — фальсификатор: без неё стенд подтверждал бы
только то, что форков нет НИГДЕ, а нам нужно, чтобы они были доступны ЯВНО.
"""
import json
import pathlib
import shutil
import subprocess
import sys
import tempfile

ЗДЕСЬ = pathlib.Path(__file__).resolve().parent
ПРИБОР = ЗДЕСЬ / "atomstore.py"
ok = fail = 0


def check(имя, cond, why=""):
    global ok, fail
    if cond:
        ok += 1; print(f"  OK   {имя}")
    else:
        fail += 1; print(f"  FAIL {имя}  {why}")


src = pathlib.Path(tempfile.mkdtemp())
(src / "t.md").write_text(
    "Первый абзац.\n\nВторой абзац.\n\nТретий абзац, подлиннее прочих.\n",
    encoding="utf-8")
store = pathlib.Path(tempfile.mkdtemp())
tasks = pathlib.Path(tempfile.mkdtemp())


def run(*args):
    return subprocess.run([sys.executable, str(ПРИБОР), "atomize", *args],
                          capture_output=True, text=True)


def units(corpus):
    f = store / corpus / "t.md.atoms.jsonl"
    if not f.exists():
        return []
    return [json.loads(l) for l in f.read_text(encoding="utf-8").splitlines() if l.strip()]


print("СТЕНД: форк не режет стор по умолчанию")

# 1. УМОЛЧАНИЕ — МАШИНА, и она добирает абзацы до 2000 знаков.
r = run("A", str(src), "--store", str(store))
u = units("A")
check("умолчание не зовёт форк (0 токенов в отчёте)",
      "БЕЗ форков" in r.stdout, r.stdout.strip()[:120])
check("умолчание ДОБИРАЕТ: три абзаца слиплись в одну единицу",
      len(u) == 1, f"{len(u)} единиц")
check("единица помечена raw, а не выдана за извлечённый атом",
      u and u[0].get("kind") == "raw", u[:1])
check("задач форкам НЕ создано",
      not list(tasks.glob("*")), list(tasks.glob("*")))

# 2. САМОСТОЯТЕЛЬНЫЕ ЕДИНИЦЫ: --min-chars 0 возвращает поштучность.
run("B", str(src), "--store", str(store), "--min-chars", "0", "--min-words", "1")
check("--min-chars 0 = поштучно (афоризмы, теоремы, клаузы)",
      len(units("B")) == 3, f"{len(units('B'))} единиц")

# 3. ФАЛЬСИФИКАТОР: форковый путь НЕ удалён, он вызывается ЯВНО и ГРОМКО.
r3 = run("C", str(src), "--store", str(store), "--fork", "--tasks", str(tasks))
check("--fork всё ещё работает (путь не выпилен)",
      r3.returncode == 0, r3.stderr[:150])
check("--fork ГРОМКО говорит, что тратит токены",
      "ФОРК" in r3.stderr and "токен" in r3.stderr, r3.stderr[:150])

# 4. ЛОВУШКА: --batch без --fork бессмыслен и обязан ОТКАЗАТЬ, а не молчать.
r4 = run("D", str(src), "--store", str(store), "--batch")
check("--batch без --fork отказывает",
      "ОТКАЗ" in r4.stderr, r4.stderr[:150])
check("и отказ виден кодом возврата, а не только текстом",
      r4.returncode == 2, f"код {r4.returncode}")

for d in (src, store, tasks):
    shutil.rmtree(d, ignore_errors=True)
print(f"\n{ok} OK, {fail} FAIL")
print("NO-FORK GREEN" if not fail else "NO-FORK RED")
sys.exit(1 if fail else 0)
