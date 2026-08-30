# -*- coding: utf-8 -*-
"""Стенд на обратный ход. Считает не только «сходится ли», но и то, что
прибор НЕ МОЖЕТ соврать молча: пустое семейство обязано быть названо, а
минимальность — проверена, а не обещана.

Ключевой контроль — ВТОРАЯ НЕЗАВИСИМАЯ ДОРОГА: ширина, посчитанная прибором
`inventory/width/bench.py`, обязана совпасть с размером наименьшего набора
из `backward`. Один и тот же ответ двумя разными кодами.
"""

import itertools
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.dirname(HERE))

from backward import backward, order          # noqa: E402
from ztl import T, F, Z, ev                   # noqa: E402

OK = FAIL = 0


def check(name, cond, detail=""):
    global OK, FAIL
    if cond:
        OK += 1
        print(f"  OK   {name}")
    else:
        FAIL += 1
        print(f"  FAIL {name}  {detail}")


def width_second_route(phi, m):
    """НЕЗАВИСИМАЯ дорога: наименьшее k, при котором СУЩЕСТВУЕТ заполнение
    k оснований, сдвигающее ЗНАЧЕНИЕ формулы. Не зовёт backward."""
    marks = [a for a, v in sorted(m.items()) if v == Z]
    base = ev(phi, m)
    for k in range(1, len(marks) + 1):
        for S in itertools.combinations(marks, k):
            for vals in itertools.product((T, F), repeat=k):
                m2 = dict(m); m2.update(dict(zip(S, vals)))
                if ev(phi, m2) != base:
                    return k
    return None


def antichain(family):
    return not any(set(a) < set(b) for a in family for b in family if a != b)


print("СТЕНД: обратный ход от результата к минимальным наборам входов")

# 1. СОВМЕСТНОСТЬ. and требует ОБА вместе; or — любой из двух.
r_and = backward(("and", "p", "q"), {"p": Z, "q": Z}, "EARNED")
r_or = backward(("or", "p", "q"), {"p": Z, "q": Z}, "EARNED")
check("and(p,q): единственный минимальный набор — оба вместе",
      r_and["possible"] == [("p", "q")], r_and["possible"])
check("or(p,q): два минимальных набора по одному",
      sorted(r_or["possible"]) == [("p",), ("q",)], r_or["possible"])
check("совместность РАЗЛИЧЕНА: размеры наборов разошлись",
      len(r_and["possible"][0]) == 2 and len(r_or["possible"][0]) == 1)

# 2. МИНИМАЛЬНОСТЬ — проверена, а не обещана.
for nm, r in (("and", r_and), ("or", r_or)):
    check(f"{nm}: possible — антицепь", antichain(r["possible"]))
    check(f"{nm}: guaranteed — антицепь", antichain(r["guaranteed"]))

# 3. ВОЗМОЖНОСТЬ ≠ ГАРАНТИЯ. Иначе различение бутафорское.
check("and(p,q): цель возможна, но НЕ гарантирована",
      r_and["possible"] and r_and["guaranteed_none"])
r_lem = backward(("or", "p", ("not", "p")), {"p": Z}, "EARNED")
check("or(p,¬p): проверка p ГАРАНТИРУЕТ цель при любом исходе",
      r_lem["guaranteed"] == [("p",)], r_lem["guaranteed"])

# 4. ПУСТОЕ СЕМЕЙСТВО НАЗВАНО, А НЕ ПРОМОЛЧАНО.
r_dead = backward(("and", "p", "q"), {"p": F, "q": Z}, "EARNED")
check("недостижимая цель: possible пуст И помечен флагом",
      r_dead["possible"] == [] and r_dead["possible_none"] is True)
check("недостижимая цель: наряд говорит НЕТ НАБОРА вслух",
      "НЕТ НАБОРА" in order(("and", "p", "q"), {"p": F, "q": Z}, "EARNED"))

# 5. УЖЕ ДОСТИГНУТО — не выписывать наряд на пустом месте.
r_done = backward(("and", "p", "q"), {"p": T, "q": T}, "EARNED")
check("цель уже достигнута: already=True", r_done["already"] is True)
check("наряд на достигнутое: 'проверять нечего'",
      "проверять нечего" in order(("and", "p", "q"), {"p": T, "q": T}, "EARNED"))

# 6. НАРЯД ВЫПИСЫВАЕТСЯ ПО ГАРАНТИИ, А ВОЗМОЖНОСТЬ НАЗВАНА СВОИМ ИМЕНЕМ.
check("без гарантии наряд честно говорит ГАРАНТИИ НЕТ",
      "ГАРАНТИИ НЕТ" in order(("and", "p", "q"), {"p": Z, "q": Z}, "EARNED"))
check("с гарантией наряд говорит 'в любом случае'",
      "в любом случае" in order(("or", "p", ("not", "p")), {"p": Z}, "EARNED"))

# 7. ВТОРАЯ НЕЗАВИСИМАЯ ДОРОГА: ширина == размер наименьшего набора.
# Считаем по ЗНАЧЕНИЮ (by_disposition=False), потому что вторая дорога
# смотрит на сдвиг значения, а не диспозиции — сравнивать надо сравнимое.
OPS = ("and", "or", "imp", "xor", "xnor")
agree = disagree = 0
for op in OPS:
    for c in itertools.product((T, F, Z), repeat=2):
        m = {"p": c[0], "q": c[1]}
        phi = (op, "p", "q")
        w2 = width_second_route(phi, m)
        base = ev(phi, m)
        # наименьший набор, СДВИГАЮЩИЙ значение = набор для любой цели != base
        sizes = []
        for tgt in (T, F, Z):
            if tgt == base:
                continue
            r = backward(phi, m, tgt, by_disposition=False)
            sizes += [len(S) for S in r["possible"]]
        w1 = min(sizes) if sizes else None
        if w1 == w2:
            agree += 1
        else:
            disagree += 1
            print(f"       расхождение {op} {c}: backward {w1}, вторая {w2}")
check(f"две дороги сошлись на всех {agree + disagree} клетках",
      disagree == 0, f"{disagree} расхождений")

print(f"\n{OK} OK, {FAIL} FAIL")
print("BACKWARD GREEN" if FAIL == 0 else "BACKWARD RED")
sys.exit(1 if FAIL else 0)
