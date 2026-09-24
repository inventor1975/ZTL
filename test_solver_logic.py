# -*- coding: utf-8 -*-
"""
test_solver_logic — the solver may use only what the claim COMMITS to.

MEASURED 2026-09-24 on the live studio (and on the morning's code): with x = ?,
`x == 2 | x == 3`, `~(x == 2)` and `x == 2 -> x == 3` all came back REFUTED,
though x = 2, 3 and 5 make them true. Every equality of the claim was taken as
a constraint, wherever it stood; the solver's own docstring promises
"propagation runs over CONJUNCTIONS of comparisons only". The same day's
quadratic path inherited it: `~(x*x == 4)` went from OPEN to REFUTED.

The check is brute force over the integers -6..6, for claims built from atoms
with every connective: REFUTED must leave no integer that makes the claim
true; an EARNED answer's solved values must make it true.
Run: python3 test_solver_logic.py  ->  SOLVER LOGIC GREEN
"""
import itertools
import sys

import zfl

ATOMS = ["x == 2", "x == 3", "x > 0", "x <= -1", "x*x == 4", "x*x - 2*x + 5 == 0",
         "x + 1 == 3", "x*x - 5*x + 6 == 0"]
SHAPES = ["{a}", "~({a})", "({a}) | ({b})", "({a}) & ({b})", "({a}) -> ({b})",
          "({a}) ^ ({b})", "~(({a}) & ({b}))"]
DOMAIN = range(-6, 7)


def truth(claim, x):
    py = (claim.replace("~", " not ").replace("->", " <= ").replace("|", " or ")
          .replace("&", " and ").replace("^", " != "))
    # the connectives above only ever join parenthesised comparisons
    return bool(eval(py, {}, {"x": x}))


checked = lies = 0
bad = []
for shape in SHAPES:
    pairs = [(a, a) for a in ATOMS] if "{b}" not in shape else itertools.product(ATOMS, ATOMS)
    for a, b in pairs:
        claim = shape.format(a=a, b=b)
        doc = {"rows": [{"name": "x", "means": "the number sought", "status": "unverified",
                         "value": "?"}], "claim": claim}
        r = zfl.run(doc)
        if not r["ok"]:
            continue
        n = r["report"]["numeric"]
        checked += 1
        witnesses = [x for x in DOMAIN if truth(claim, x)]
        d = n["disposition"]
        if d == "REFUTED" and witnesses:
            lies += 1
            bad.append(f"REFUTED but true at x = {witnesses[0]}: {claim}")
        if d == "EARNED":
            sx = n["solved"].get("x") or {}
            vals = sx.get("roots") or ([sx["lo"]] if sx.get("pinned") else [])
            for v in vals:
                if v.startswith("≈"):
                    continue
                from fractions import Fraction
                fv = Fraction(v)
                if fv.denominator == 1 and not truth(claim, int(fv)):
                    lies += 1
                    bad.append(f"EARNED with x = {v}, which makes it false: {claim}")
for line in bad[:12]:
    print("LIE:", line)
if lies:
    print(f"FAIL: {lies} lies in {checked} claims")
    sys.exit(1)
print(f"SOLVER LOGIC GREEN — {checked} claims, 0 lies")
