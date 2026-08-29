#!/usr/bin/env python3
# Copyright 2026 Vitaly Reznik
# SPDX-License-Identifier: Apache-2.0
"""Стенд: совместный наряд НЕ выдаётся на уже решённом.

Зачем. `_joint` отвечает: «ни одно основание не двигает вердикт — значит нужны
все вместе». На НАСЛЕДСТВЕННОМ вердикте ни одно и не двигает, потому что двигать
нечего. Тавтология `imp(and(a,b), a)` верна при любых a и b — и движок велел
проверить ОБА основания. Это первый рог Менона: наряд на уже решённое. В `judge`
охрана стояла с 2026-08-19 (joint гасится при EARNED/REFUTED/E), в движок она не
дошла.

Каждая проверка с КОНТРОЛЕМ. Погасить наряд на тавтологии легко — легко и
погасить его везде; поэтому честный ШИРОКИЙ случай обязан наряд сохранить,
иначе стенд доволен прибором, который просто вырезал полезное.
"""
import json
import pathlib
import sys

ЗДЕСЬ = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(ЗДЕСЬ))
sys.path.insert(0, str(ЗДЕСЬ.parent))

import engine  # noqa: E402
import zfl     # noqa: E402

ok = fail = 0


def check(имя, cond, why=""):
    global ok, fail
    if cond:
        ok += 1
        print(f"  OK   {имя}")
    else:
        fail += 1
        print(f"  FAIL {имя} — {why}")


def отчёт(expr, atoms=("a", "b")):
    doc = json.dumps({"genre": "statement",
                      "atoms": {x: {"status": "Z"} for x in atoms},
                      "assert": expr})
    d, p, iss = zfl.validate(doc)
    беды = [i for i in iss if i["level"] == "error"]
    assert not беды, f"{expr}: {беды}"
    return engine.run(d, p)


t = отчёт("imp(and(a, b), a)")
check("тавтология: вердикт наследственный", t["warranty"] == "hereditary", str(t["warranty"]))
check("тавтология НЕ получает совместного наряда", not t.get("joint"),
      "наряд на уже решённом — первый рог Менона")

ш = отчёт("xnor(a, b)")
check("КОНТРОЛЬ: честный ШИРОКИЙ случай наряд СОХРАНИЛ", bool(ш.get("joint")),
      "охрана вырезала и полезное — прибор стал молчать вместо того, чтобы точнее говорить")
check("КОНТРОЛЬ: у широкого вердикт НЕ наследственный",
      ш["warranty"] != "hereditary", str(ш["warranty"]))

у = отчёт("and(a, b)")
check("КОНТРОЛЬ: узкий случай наряда и не имел", not у.get("joint"),
      "здесь одно основание двигает дело, совместному наряду взяться неоткуда")

check("КОНТРОЛЬ: охрана смотрит на НАСЛЕДСТВЕННОСТЬ, а не на вердикт",
      t["verdict"] != ш["verdict"] or t["warranty"] != ш["warranty"],
      "тавтология и широкий случай неразличимы — стенд ничего не проверяет")

print(f"\nJOINT-NOT-ON-SETTLED {'GREEN' if not fail else 'RED'}: {ok} OK, {fail} FAIL")
sys.exit(1 if fail else 0)
