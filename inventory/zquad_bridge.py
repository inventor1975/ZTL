# -*- coding: utf-8 -*-
"""
znumsolve._parabola_pieces ↔ lean/ZQuad.lean — the code computes the theorem's intervals (2026-11-27).

`lean/ZQuad.lean` proves over any ordered commutative ring (no axioms), t = 2q·x + p, d = p² − 4qc:
q ≥ 0, f(x) ≤ 0 ⇒ t² ≤ d (inside the roots); q ≤ 0, f(x) ≤ 0 ⇒ d ≤ t² (outside); f(x) = 0 ⇒ t² = d.
The rest — |t| ≤ s_hi from t² ≤ d ≤ s_hi², and dividing by 2q — is ℚ's decided order and exact arithmetic, named as a
premise there. This stand checks, on seeded random parabolas with integer coefficients (both signs of q, d < 0, = 0,
> 0, square and non-square), that:
  1. the clamp `_rat_sqrt(d)` brackets √d: s_lo ≥ 0, s_lo² ≤ d ≤ s_hi² (the premise holds where the code uses it);
  2. the pieces are EXACTLY the theorem's intervals, clipped to the box: `le`, q > 0 — [(−p − s_hi)/2q, (−p + s_hi)/2q];
     q < 0 — (−∞, (−p + s_lo)/2q]… written as the code's two half-lines; `eq` — the two root brackets;
  3. SOUNDNESS on points: every rational on a fine grid of the box that satisfies the constraint lies in some piece;
  4. both sides: some cases have points outside every piece (the narrowing narrows) and some have pieces = [].
MUTATION: both clamp ends replaced by s_lo / 2 (a clamp below √d) -> check 3 finds a dropped solution.

Run:  python3 inventory/zquad_bridge.py   -> ZQUAD BRIDGE GREEN
"""
import os
import random
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
import znumsolve as S                  # noqa: E402
from znum import INF, _rat_sqrt        # noqa: E402


def f(q, p, c, x):
    return q * x * x + p * x + c


def theorem_sets(kind, p, q, c, s_lo, s_hi):
    d = p * p - 4 * q * c
    if d < 0:
        return [] if (kind == "eq" or q > 0) else [(-INF, INF)]
    sg = [((-p - s_lo) / (2 * q), (-p - s_hi) / (2 * q)), ((-p + s_lo) / (2 * q), (-p + s_hi) / (2 * q))]
    roots = sorted((min(a), max(a)) for a in sg)
    if d == 0:
        roots = roots[:1]
    if kind == "eq":
        return roots
    if q > 0:
        return [(roots[0][0], roots[-1][1])]
    return [(-INF, roots[0][1]), (roots[1][0], INF)] if len(roots) == 2 else [(-INF, INF)]


def clip(sets, box):
    out = []
    for lo, hi in sets:
        lo, hi = max(lo, box["lo"]), min(hi, box["hi"])
        if lo <= hi:
            out.append((lo, hi))
    return out


def main(mutate=False):
    rnd = random.Random(20261127)
    ok = fail = narrowed = empty = 0
    for _ in range(400):
        q = rnd.choice([x for x in range(-4, 5) if x != 0])
        p = rnd.randint(-9, 9)
        c = rnd.randint(-9, 9)
        kind = rnd.choice(["le", "eq"])
        box = {"lo": Fr(-6), "hi": Fr(6)}
        d = p * p - 4 * q * c
        pieces = S._parabola_pieces(kind, Fr(p), Fr(q), Fr(c), box)
        good = True
        if d >= 0:
            s_lo, s_hi = _rat_sqrt(Fr(d))
            if mutate:
                s_lo = s_hi = s_lo / 2
            good &= s_lo >= 0 and s_lo * s_lo <= d <= s_hi * s_hi or mutate
            want = clip(theorem_sets(kind, Fr(p), Fr(q), Fr(c), s_lo, s_hi), box)
        else:
            want = clip(theorem_sets(kind, Fr(p), Fr(q), Fr(c), 0, 0), box)
        if not mutate:
            good &= pieces == want
        use = want if mutate else pieces
        grid = [box["lo"] + Fr(k, 40) for k in range(0, 481)]
        sols = [x for x in grid if (f(q, p, c, x) == 0 if kind == "eq" else f(q, p, c, x) <= 0)]
        inside = all(any(lo <= x <= hi for lo, hi in use) for x in sols)
        good &= inside
        narrowed += any(not any(lo <= x <= hi for lo, hi in use) for x in grid)
        empty += use == []
        ok += good; fail += not good
    return ok, fail, narrowed, empty


if __name__ == "__main__":
    ok, fail, narrowed, empty = main()
    print(f"parabolas 400 (q of both signs, d < 0 / = 0 / > 0): clamp holds and pieces == the theorem's intervals and "
          f"every grid solution inside: {ok}, differ {fail}; narrowing removes grid points in {narrowed}; no piece in {empty}")
    mok, mfail, _, _ = main(mutate=True)
    caught = mfail > 0
    print(f"mutation (clamp too narrow): {'caught' if caught else 'NOT CAUGHT'} ({mfail} cases drop a solution)")
    if fail == 0 and narrowed > 0 and empty > 0 and caught:
        print("ZQUAD BRIDGE GREEN")
    else:
        print("ZQUAD BRIDGE RED"); sys.exit(1)
