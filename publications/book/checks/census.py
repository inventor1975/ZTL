# -*- coding: utf-8 -*-
"""Потери жадного регистра: требуют ли они кратности вхождений?

В книге (гл. 9) «потери» с 2026-10-25 называются «отложенным да»: Z — грязный
параметр, и терпеливый судья, давая «да», молча считает, что хозяин его не
поменял. Сверка с грязным чтением — dirty_census.py рядом."""
import os, sys, itertools, random, collections
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from ztl import T, F, Z, ev
from ztljudge import _show

OPS2 = ("and", "or", "imp", "xor", "xnor")


def counts(phi, acc=None):
    acc = collections.Counter() if acc is None else acc
    if isinstance(phi, str):
        acc[phi] += 1
    else:
        for s in phi[1:]:
            counts(s, acc)
    return acc


def audit(phi, m, atoms):
    marks = [a for a in atoms if m[a] == Z]
    if not marks:
        return None
    comps = [ev(phi, {**m, **dict(zip(marks, v))})
             for v in itertools.product((T, F), repeat=len(marks))]
    v = ev(phi, m)
    c = counts(phi)
    multi = any(c[a] >= 2 for a in marks)          # помеченный атом встречается >= 2 раз
    loss = all(x == T for x in comps) and v != T
    gift = v == T and any(x != T for x in comps)
    return loss, gift, multi


def run(name, pairs, atoms):
    n = collections.Counter()
    wit = []
    for phi, m in pairs:
        r = audit(phi, m, atoms)
        if r is None:
            continue
        loss, gift, multi = r
        n["cells"] += 1
        n["multi" if multi else "single"] += 1
        if loss:
            n["loss_multi" if multi else "loss_SINGLE"] += 1
            if not multi and len(wit) < 4:
                wit.append((_show(phi), dict(m)))
        if gift:
            n["gift_multi" if multi else "gift_single"] += 1
    print(f"\n  {name}")
    print(f"    клеток с меткой                    {n['cells']}")
    print(f"      из них кратность >=2             {n['multi']}")
    print(f"      из них кратность 1               {n['single']}")
    print(f"    ПОТЕРИ при кратности >=2           {n['loss_multi']}")
    print(f"    ПОТЕРИ при кратности 1             {n['loss_SINGLE']}   <-- T1 требует НОЛЬ")
    print(f"    подарки при кратности >=2          {n['gift_multi']}")
    print(f"    подарки при кратности 1            {n['gift_single']}   <-- T2 требует >0")
    if n["multi"]:
        print(f"    доля потерь среди кратных          "
              f"{100*n['loss_multi']//n['multi']}%")
    for w in wit:
        print(f"    ИСКЛЮЧЕНИЕ: {w[0]}  {w[1]}")
    return n["loss_SINGLE"]


# A. исчерпывающе, глубина <=2, три атома
A = ("p", "q", "r")
d0 = list(A)
d1 = [("not", a) for a in d0] + [(o, a, b) for o in OPS2 for a in d0 for b in d0]
base = d0 + d1
d2 = [("not", f) for f in d1] + [(o, a, b) for o in OPS2 for a in base for b in base]
pool, seen = [], set()
for f in d0 + d1 + d2:
    if f not in seen:
        seen.add(f); pool.append(f)
print("=" * 66)
print("ТРЕБУЮТ ЛИ ПОТЕРИ КРАТНОСТИ ВХОЖДЕНИЙ?")
print("=" * 66)
print(f"A: {len(pool)} формул x {3**len(A)} разметок")
bad = run("A. исчерпывающе, глубина<=2, три атома",
          ((f, dict(zip(A, c))) for f in pool
           for c in itertools.product((T, F, Z), repeat=len(A))), A)

# B. случайные глубокие
B = ("p", "q", "r", "s")
rnd = random.Random(20260820)
def grow(d):
    if d == 0 or rnd.random() < 0.2: return rnd.choice(B)
    if rnd.random() < 0.25: return ("not", grow(d - 1))
    return (rnd.choice(OPS2), grow(d - 1), grow(d - 1))
bad += run("B. случайные, глубина<=6, четыре атома",
           [(grow(6), {a: rnd.choice((T, F, Z)) for a in B}) for _ in range(40000)], B)

print("\n" + "=" * 66)
print("T1 ДЕРЖИТСЯ — потерь при кратности 1 нет" if bad == 0
      else f"T1 ОПРОВЕРГНУТА — {bad} исключений")
