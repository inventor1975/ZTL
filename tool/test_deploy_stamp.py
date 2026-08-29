#!/usr/bin/env python3
# Copyright 2026 Vitaly Reznik
# SPDX-License-Identifier: Apache-2.0
"""Стенд: отпечаток развёрнутого экземпляра ловит подмену и не молчит без себя.

Зачем. 2026-08-29: дерево студии на сервере — не гит, и по живому экземпляру
нельзя было сказать, что там крутится. Отпечаток отвечает на вопрос «совпадает
ли лежащее с объявленным» — и обязан ПЕРЕСЧИТЫВАТЬ, а не читать объявленное.

Каждая проверка с КОНТРОЛЕМ: показать, что сходится, мало — надо показать, что
НЕ сходится, когда файл тронут, появился или пропал. Прибор, который всегда
говорит «сходится», не прибор.
"""
import pathlib, shutil, subprocess, sys, tempfile

ЗДЕСЬ = pathlib.Path(__file__).resolve().parent
ПРИБОР = ЗДЕСЬ / "deploy_stamp.py"

ok = fail = 0
def check(имя, cond, why=""):
    global ok, fail
    if cond: ok += 1; print(f"  OK   {имя}")
    else: fail += 1; print(f"  FAIL {имя} — {why}")

def гон(*args, корень):
    r = subprocess.run([sys.executable, str(ПРИБОР), *args, str(корень)],
                       capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr

d = pathlib.Path(tempfile.mkdtemp())
(d / "a.py").write_text("x = 1\n", encoding="utf-8")
(d / "sub").mkdir()
(d / "sub" / "b.py").write_text("y = 2\n", encoding="utf-8")

код, вывод = гон("--check", корень=d)
check("без отпечатка — ОТКАЗ, а не молчаливое «всё хорошо»", код == 2 and "ОТПЕЧАТКА НЕТ" in вывод, вывод[:120])

код, вывод = гон("--write", корень=d)
check("отпечаток записывается", код == 0 and (d / "DEPLOYED.json").exists())
check("считает файлы в подкаталогах", "2 файлов" in вывод, вывод[:80])

код, вывод = гон("--check", корень=d)
check("нетронутое дерево СХОДИТСЯ", код == 0 and "СХОДИТСЯ" in вывод, вывод[:120])

(d / "a.py").write_text("x = 999\n", encoding="utf-8")
код, вывод = гон("--check", корень=d)
check("КОНТРОЛЬ: изменённый файл пойман", код == 1 and "ИЗМЕНЁН" in вывод and "a.py" in вывод, вывод[:160])

(d / "a.py").write_text("x = 1\n", encoding="utf-8")
(d / "новый.py").write_text("z = 3\n", encoding="utf-8")
код, вывод = гон("--check", корень=d)
check("КОНТРОЛЬ: ПОЯВИВШИЙСЯ файл пойман", код == 1 and "ПОЯВИЛСЯ" in вывод, вывод[:160])

(d / "новый.py").unlink()
(d / "sub" / "b.py").unlink()
код, вывод = гон("--check", корень=d)
check("КОНТРОЛЬ: ПРОПАВШИЙ файл пойман", код == 1 and "ПРОПАЛ" in вывод, вывод[:160])

check("КОНТРОЛЬ: отпечаток САМ говорит, чего не доказывает",
      "НЕ доказывает одобренность" in (d / "DEPLOYED.json").read_text(encoding="utf-8"),
      "граница не записана в самом артефакте, и её потеряют")

shutil.rmtree(d, ignore_errors=True)
print(f"\nDEPLOY-STAMP {'GREEN' if not fail else 'RED'}: {ok} OK, {fail} FAIL")
sys.exit(1 if fail else 0)
