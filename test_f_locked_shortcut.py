# -*- coding: utf-8 -*-
"""Сокращение `f_locked` в `zverify.hereditary_bit` — РАВНОСИЛЬНО перебору.

Теорема доказана в Lean на пустом списке аксиом, но доказанная теорема и
верно подключённая теорема — разные вещи. Здесь проверяется ВТОРОЕ: что
сокращение отвечает ровно то же, что полный обход 3^n, на исчерпывающем поле.

Проверяется и обратное: что оно вообще СРАБАТЫВАЕТ. Сокращение, которое
никогда не включается, тоже «не расходится с перебором» — и это был бы
ложный зелёный.
"""
import itertools
import sys

from ztl import T, F, Z
from zverify import (hereditary_bit, f_locked_by_markfree_conjunct,
                     refinements, ztl_eval)

OPS = ("and", "or", "imp", "xor", "xnor")


def forms(atoms, depth):
    if depth == 0:
        for a in atoms:
            yield a
            yield ("not", a)
        return
    for f in forms(atoms, depth - 1):
        yield f
    for op in OPS:
        for l in forms(atoms, depth - 1):
            for r in forms(atoms, depth - 1):
                yield (op, l, r)


def brute(phi, m):
    v = ztl_eval(phi, m)
    return all(ztl_eval(phi, m2) == v for m2 in refinements(m))


ok = fail = 0


def check(name, cond, why=""):
    global ok, fail
    if cond:
        ok += 1; print(f"  OK   {name}")
    else:
        fail += 1; print(f"  FAIL {name}  {why}")


print("СТЕНД: сокращение f_locked не расходится с перебором")
atoms = ("p", "q")
pairs = fires = diverge = 0
examples = []
for phi in forms(atoms, 2):
    for c in itertools.product((T, F, "M"), repeat=2):
        m = dict(zip(atoms, c))
        pairs += 1
        if f_locked_by_markfree_conjunct(phi, m):
            fires += 1
            if not brute(phi, m):
                diverge += 1
                if len(examples) < 3:
                    examples.append((phi, m))

print(f"  пар (формула, разметка) проверено: {pairs}")
print(f"  сокращение сработало             : {fires}")
print(f"  расхождений с перебором          : {diverge}")
check("расхождений НЕТ", diverge == 0, examples[:2])
check("ФАЛЬСИФИКАТОР: сокращение вообще срабатывает", fires > 0,
      "иначе зелёный ничего не значит")

# и полная равносильность самого hereditary_bit
diff = 0
for phi in forms(atoms, 2):
    for c in itertools.product((T, F, "M"), repeat=2):
        m = dict(zip(atoms, c))
        if hereditary_bit(phi, m) != brute(phi, m):
            diff += 1
check("hereditary_bit совпадает с перебором на всём поле", diff == 0, f"{diff} расхождений")

# три атома — шире
atoms3 = ("p", "q", "r")
d3 = f3 = 0
for phi in forms(atoms3, 1):
    for c in itertools.product((T, F, "M"), repeat=3):
        m = dict(zip(atoms3, c))
        if f_locked_by_markfree_conjunct(phi, m):
            f3 += 1
            if not brute(phi, m):
                d3 += 1
check(f"три атома: {f3} срабатываний, расхождений {d3}", d3 == 0 and f3 > 0)

print(f"\n{ok} OK, {fail} FAIL")
print("F-LOCKED SHORTCUT GREEN" if not fail else "F-LOCKED SHORTCUT RED")
sys.exit(1 if fail else 0)
