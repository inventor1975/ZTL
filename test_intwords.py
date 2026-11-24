# -*- coding: utf-8 -*-
"""test_intwords — the integer words on the numeric floor (idiv, mod, dvd, fact, choose), the twin of
VR/Numbers/Division.lean (every object there on []), tested from both sides (2026-11-24).

    python3 test_intwords.py

1. Points, against Python's own integers: Euclidean idiv/mod, divisibility (0 | 0 holds, 0 | b fails for b != 0 — the
   definition's consequence), n!, C(n, k) (0 for k > n).
2. NO CONVENTION VALUE: idiv/mod by a pinned 0 has no reading (E) — Lean's 7 / 0 = 0 and 7 % 0 = 7 are conventions;
   a non-integer point has no reading; a negative argument (exists in Z, not read by the VR twin) is a mark, not E.
3. The other side: over small integer boxes, every forced verdict holds at every lattice point (brute force)."""
import itertools
import math
import sys

from znumjudge import judge_sheet_claim, parse_quantities

FAILS, N = [], [0]


def disp(claim, sheet=""):
    q, m = parse_quantities(sheet) if sheet else ({}, {})
    return judge_sheet_claim(claim, q, m)["disposition"]


def check(cond, what):
    N[0] += 1
    if not cond:
        FAILS.append(what)
        print("FAIL", what)


# 1. points
for a, b in itertools.product(range(0, 13), range(1, 6)):
    check(disp(f"idiv({a}, {b}) == {a // b}") == "EARNED" and disp(f"mod({a}, {b}) == {a % b}") == "EARNED",
          f"idiv/mod at ({a}, {b})")
for a, b in itertools.product(range(-6, 7), range(-12, 13)):
    want = 1 if (b == 0 if a == 0 else b % abs(a) == 0) else 0
    check(disp(f"dvd({a}, {b}) == {want}") == "EARNED", f"dvd({a}, {b}) = {want}")
for n in range(0, 12):
    check(disp(f"fact({n}) == {math.factorial(n)}") == "EARNED", f"fact({n})")
    for k in range(0, 14):
        check(disp(f"choose({n}, {k}) == {math.comb(n, k) if k <= n else 0}") == "EARNED", f"choose({n}, {k})")
# 2. no convention value
for c in ("idiv(7, 0) == 0", "mod(7, 0) == 7", "idiv(0, 0) == 0", "mod(7/2, 2) == 1", "fact(5/2) >= 0"):
    check(disp(c) == "E", f"{c}: no reading")
for c in ("fact(0-1) >= 0", "idiv(0-7, 2) <= 0", "choose(0-1, 0) >= 0"):
    check(disp(c) == "OPEN", f"{c}: exists in Z, the twin does not read it — a mark")
check(disp("mod(x, 3) <= 2", "x=[0,10] earned:a") == "OPEN", "a continuous range: a mark")
# 3. the other side, brute force over small boxes
for (lo, hi), d in itertools.product([(0, 6), (3, 9), (0, 20)], [1, 2, 3, 5]):
    for bound in range(-1, 7):
        for word, f in (("mod", lambda x: x % d), ("idiv", lambda x: x // d)):
            sh = f"n=[{lo},{hi}] earned:a int"
            v = disp(f"{word}(n, {d}) <= {bound}", sh)
            if v in ("EARNED", "REFUTED"):
                vals = [f(x) for x in range(lo, hi + 1)]
                check(all((x <= bound) == (v == "EARNED") for x in vals), f"soundness: {word}(n,{d}) <= {bound} over {sh}: {v}")
for (lo, hi) in [(0, 5), (2, 7)]:
    for bound in (1, 2, 24, 120, 5040):
        sh = f"n=[{lo},{hi}] earned:a int"
        v = disp(f"fact(n) <= {bound}", sh)
        if v in ("EARNED", "REFUTED"):
            check(all((math.factorial(x) <= bound) == (v == "EARNED") for x in range(lo, hi + 1)),
                  f"soundness: fact(n) <= {bound} over {sh}: {v}")

print(f"INTWORDS GREEN — {N[0]} checks" if not FAILS else f"test_intwords: {len(FAILS)} failures of {N[0]}")
sys.exit(1 if FAILS else 0)
