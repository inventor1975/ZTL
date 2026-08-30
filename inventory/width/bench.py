# -*- coding: utf-8 -*-
"""How many grounds must be filled TOGETHER before anything moves?"""
import os, sys, itertools, random
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from ztljudge import judge, _show, _lazy
from ztl import T, F, Z, ev
from ztime import depth2_pool

TERMINAL = {"EARNED", "REFUTED"}


def width(phi, m, atoms):
    """Smallest number of unverified grounds whose JOINT filling moves the
    verdict. Returns None if no subset moves it at all."""
    marks = [a for a in atoms if m[a] == Z]
    base = ev(phi, m)
    for k in range(1, len(marks) + 1):
        for S in itertools.combinations(marks, k):
            for vals in itertools.product((T, F), repeat=k):
                m2 = dict(m); m2.update(dict(zip(S, vals)))
                if ev(phi, m2) != base:
                    return k
    return None


def chain(n):
    """p0 ⊕ p1 ⊕ … ⊕ p(n-1), left-assoc — the shape predicted to grow."""
    f = "p0"
    for i in range(1, n):
        f = ("xor", f, f"p{i}")
    return f


print("=" * 70)
print("IS THE WIDTH OF AN INQUIRY BOUNDED?")
print("=" * 70)
print("\n  A. the predicted witness: xor chains, every ground unverified")
for n in range(2, 9):
    phi = chain(n)
    atoms = tuple(f"p{i}" for i in range(n))
    m = {a: Z for a in atoms}
    w = width(phi, m, atoms)
    print(f"    {n} marks -> verdict {ev(phi, m)}   width {w}")

print("\n  B. distribution over the depth-2 pool (p, q), unsettled cells only")
dist = {}
A = ("p", "q")
for phi in depth2_pool():
    for c in itertools.product((T, F, Z), repeat=2):
        m = dict(zip(A, c))
        if judge(_show(phi), m)["disposition"] in TERMINAL:
            continue
        w = width(phi, m, A)
        dist[w] = dist.get(w, 0) + 1
tot = sum(dist.values())
for k in sorted(dist, key=lambda x: (x is None, x)):
    print(f"    width {str(k):5} {dist[k]:7}  ({100*dist[k]//max(tot,1)}%)")

print("\n  C. random depth<=5 over five atoms — does width climb in the wild?")
OPS2 = ("and", "or", "imp", "xor", "xnor")
B = tuple(f"a{i}" for i in range(5))
rnd = random.Random(20260819)


def grow(d):
    if d == 0 or rnd.random() < 0.2:
        return rnd.choice(B)
    if rnd.random() < 0.25:
        return ("not", grow(d - 1))
    return (rnd.choice(OPS2), grow(d - 1), grow(d - 1))


dist2 = {}
deep = []
for _ in range(3000):
    phi = grow(5)
    m = {a: rnd.choice((T, F, Z)) for a in B}
    if judge(_show(phi), m)["disposition"] in TERMINAL:
        continue
    w = width(phi, m, B)
    dist2[w] = dist2.get(w, 0) + 1
    if w is not None and w >= 3 and len(deep) < 3:
        deep.append((_show(phi), dict(m), w))
tot2 = sum(dist2.values())
for k in sorted(dist2, key=lambda x: (x is None, x)):
    print(f"    width {str(k):5} {dist2[k]:7}  ({100*dist2[k]//max(tot2,1)}%)")
for d in deep:
    print(f"    wide: {d[0][:70]}  width {d[2]}")

print("\n  D. is width visible to the label?")
phi = chain(3)
atoms = ("p0", "p1", "p2")
m = {a: Z for a in atoms}
print(f"    {_show(phi)} all unverified: width {width(phi, m, atoms)}, "
      f"label {sorted(_lazy(phi, m)[1])}")
print("    the label names every ground and cannot say how many are needed at once.")
