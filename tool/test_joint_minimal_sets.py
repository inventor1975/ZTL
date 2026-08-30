# -*- coding: utf-8 -*-
"""Стенд на две правки ядра от 2026-08-30.

1. ГРУНТ ВНЕ ЗАЯВКИ В НАРЯД НЕ ИДЁТ. ZFL разрешает объявить атом и не
   употребить его; валидатор молчит. До правки движок на `xnor(a, c)` с
   объявленными `a,b,c,d` выдавал наряд на все четыре.
2. МИНИМАЛЬНЫЕ НАБОРЫ ВМЕСТО «ВСЕ СРАЗУ». Грубый ответ завышает наряд,
   когда хватает подмножества.
"""

import itertools
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.dirname(HERE))

import zfl                                                    # noqa: E402
import engine                                                 # noqa: E402
from ztljudge import joint_grounds, joint_sets                # noqa: E402
from ztl import T, F, Z, ev                                   # noqa: E402
from zverify import grade                                     # noqa: E402

OK = FAIL = 0
WIT = ("xor", ("not", ("and", ("or", "d", "a"), "c")),
       ("xnor", "d", ("not", ("imp", ("not", "d"), "b"))))
M4 = {x: Z for x in "abcd"}


def check(name, cond, detail=""):
    global OK, FAIL
    if cond:
        OK += 1; print(f"  OK   {name}")
    else:
        FAIL += 1; print(f"  FAIL {name}  {detail}")


def run_zfl(atoms, assertion):
    doc_text = json.dumps({"genre": "statement",
                           "atoms": {k: {"status": v} for k, v in atoms.items()},
                           "assert": assertion,
                           "ask": ["verdict", "warranty"]}, ensure_ascii=False)
    doc, parsed, issues = zfl.validate(doc_text)
    assert not [i for i in issues if i["level"] == "error"], issues
    return engine.run(doc, parsed)


print("СТЕНД: наряд не зовёт лишнее и не завышает объём")

# --- 1. грунт вне формулы
jg = joint_grounds(("xnor", "a", "c"), M4)
check("joint_grounds не берёт грунты вне формулы", jg == ["a", "c"], jg)
rep = run_zfl({"a": "Z", "b": "Z", "c": "Z", "d": "Z"}, "xnor(a, c)")
# Проверять ПЕРЕЧЕНЬ, а не подстроку: буква d сидит внутри «ground» и «and»,
# и наивный тест краснел на верном коде. Свой прибор тоже надо мерить.
listed = rep.get("joint", "").split("this: ")[-1].split(" must be")[0]
check("движок: в перечне наряда нет b и d",
      "b" not in listed and "d" not in listed, listed)
check("КОНТРОЛЬ: наряд всё-таки называет настоящие грунты a и c",
      "a" in rep.get("joint", "") and "c" in rep.get("joint", ""))

# --- 2. минимальные наборы
sets = joint_sets(WIT, M4)
check("свидетель: грубый ответ требует ВСЕ четыре",
      sorted(joint_grounds(WIT, M4)) == ["a", "b", "c", "d"])
check("наборы найдены и КАЖДЫЙ меньше четырёх",
      sets and all(len(S) < 4 for S in sets), sets)
check("наборы — антицепь (ни один не содержит другой)",
      not any(set(a) < set(b) for a in sets for b in sets if a != b), sets)


def moves(phi, m, S):
    """«Двигает» в ядре означает ВЕРДИКТ ИЛИ ГРАДУС ГАРАНТИИ, не только
    значение — так определён `_moves`. Первая редакция этого стенда мерила
    одно значение и покраснела на ВЕРНОМ коде: набор `b + c` градус двигает,
    значение нет. Стенд, говорящий на другом языке, чем прибор, меряет не
    прибор. Реализовано здесь ЗАНОВО (через `ev` и `grade`), а не вызовом
    ядра — иначе это не вторая дорога, а зеркало."""
    # ДИАЛЕКТ МЕТКИ: zverify ждёт 'M', а не Z. С Z-разметкой grade МОЛЧА
    # отвечает всегда «hereditary» — записанная яма, и я в неё зашёл: первая
    # редакция стенда краснела на верном ядре, потому что градус не видел марок.
    def g(mm):
        return grade(phi, {a: ("M" if v == Z else v) for a, v in mm.items()})
    base = (ev(phi, m), g(m))
    for v in itertools.product((T, F), repeat=len(S)):
        m2 = {**m, **dict(zip(S, v))}
        if (ev(phi, m2), g(m2)) != base:
            return True
    return False


check("КАЖДЫЙ выданный набор действительно двигает",
      all(moves(WIT, M4, S) for S in sets))
check("ФАЛЬСИФИКАТОР: ни одно ОДИНОЧНОЕ основание не двигает",
      not any(moves(WIT, M4, (a,)) for a in "abcd"))

# --- 3. когда одиночного грунта довольно — семейства НЕТ, а не пустой шум
check("одиночный грунт двигает -> joint_sets пуст",
      joint_sets(("or", "p", "q"), {"p": Z, "q": Z}) == [],
      joint_sets(("or", "p", "q"), {"p": Z, "q": Z}))

# --- 4. ПОТОЛОК НАЗВАН, А НЕ ОБОЙДЁН МОЛЧА
check("сверх потолка возвращается [] (отказ, не кривой ответ)",
      joint_sets(WIT, M4, cap=3) == [])

# --- 5. ВТОРАЯ ДОРОГА: независимый перебор даёт то же семейство
def brute(phi, m):
    unv = sorted(a for a, v in m.items() if v == Z)
    out = []
    for k in range(2, len(unv) + 1):
        for S in itertools.combinations(unv, k):
            if any(set(p) < set(S) for p in out):
                continue
            if moves(phi, m, S):
                out.append(S)
    return [list(S) for S in out]


check("вторая дорога дала то же семейство",
      sorted(map(tuple, sets)) == sorted(map(tuple, brute(WIT, M4))),
      f"{sets} vs {brute(WIT, M4)}")

print(f"\n{OK} OK, {FAIL} FAIL")
print("JOINT-MINIMAL GREEN" if FAIL == 0 else "JOINT-MINIMAL RED")
sys.exit(1 if FAIL else 0)
