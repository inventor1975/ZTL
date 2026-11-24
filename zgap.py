# -*- coding: utf-8 -*-
"""
zgap — A STRICT BOUND IS A WITNESSED GAP (2026-11-24, the curator's "Да. Делаем.").

WHY. Lean writes its guards as strict hypotheses — `0 < x`, `b ≠ 0` — and the numeric floor had only closed
intervals: `0 < x` became [0, inf], the edge 0 was a reading, and every `ln x` / `1/x` the hypothesis guards came back
OPEN (MEASURED that day: ln(x) over [0,2] -> OPEN, x/x over [0,inf] -> OPEN). zfl even refused `(0,inf]` outright
(E_OPEN_INTERVAL, "put the strictness in the claim") — but a strictness in the claim never reached the next atom:
`x > 0 & ln(x) <= x` stayed OPEN.

WHAT IT IS, from VR. In VR's operational reals (VR/Numbers/RealsOp.lean) a strict order is not a bare negation:
`rlt x y` holds when a GAP is witnessed — from some point on, y - x >= 1/2^k for a named k — and `x ≠ y` is APARTNESS,
`rapart x y := rlt x y ∨ rlt y x`. So `0 < x` says: every reading of x stands at a positive distance from 0. On the
floor's set of readings that is exactly an interval whose end 0 is EXCLUDED: (0, inf]. `Gap` marks such an end.

THE ONE RULE THAT KEEPS IT SOUND. A `Gap` is a Fraction (same value, same order, same hash), so every piece of the
floor that does not know about gaps reads the end as CLOSED — the reading set grows by one point, a verdict on the
larger set holds on the smaller (the hereditary direction), so forgetting a gap can only cost precision (an OPEN where
an EARNED was due), never produce a false verdict. Arithmetic on Fractions returns a plain Fraction, i.e. forgets.
Only the places that are taught keep it: the interval operations, the linear reading, sqrt, ln, and the comparisons,
where an excluded end decides `0 < x` (T) and `x != 0` (T) and puts ln / division inside their domains.

LEAN. The floor's closed-box theorems (lean/ZNum.lean) cover the closure; the gap rules themselves have no Lean twin
yet — a Python reading, tested both ways in test_znum_gap.py.
"""
from fractions import Fraction


class Gap(Fraction):
    """An interval END that is EXCLUDED: every reading stands at a positive (witnessed) distance from it."""

    def __repr__(self):
        return f"Gap({Fraction(self)})"


def gap(x):
    """Mark the end x as excluded (a float infinity is never attained anyway and stays as it is)."""
    if isinstance(x, float):
        return x
    return Gap(Fraction(x))


def is_gap(x):
    return isinstance(x, Gap)


def mark(x, excluded):
    """x with its exclusion set as `excluded` (a plain Fraction when not)."""
    if isinstance(x, float):
        return x
    return Gap(Fraction(x)) if excluded else Fraction(x)
