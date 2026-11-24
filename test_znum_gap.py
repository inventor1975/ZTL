# -*- coding: utf-8 -*-
"""test_znum_gap — the strict bound as a witnessed gap (zgap.py, 2026-11-24), tested from BOTH sides.

    python3 test_znum_gap.py

1. Each case below is a pair: the same claim over an interval with an EXCLUDED end (x > 0 said by `(0,...`) and over its
   closure. The gap must decide what the guard decides — and the closure must NOT (else the gap is not what decided).
2. The other side of the bracket: a forced verdict over an open box must hold at every reading. Random rational points
   strictly inside each box (and at its closed ends) are evaluated exactly; one disagreeing point fails the test.
3. `!=` is `~(==)`, `**` is the product it abbreviates, and the sheet reads `(a,b]`.
"""
import random
import sys
from fractions import Fraction

import zfl
from znumjudge import _parse_arith, parse_quantities

FAILS = []
N = [0]


def check(cond, what):
    N[0] += 1
    if not cond:
        FAILS.append(what)
        print("FAIL", what)


def verdict(value, claim, scale=None, y=None):
    rows = [{"name": "x", "status": "verified", "ground": "hyp", "value": value, "means": "x"}]
    if scale:
        rows[0]["scale"] = scale
    if y is not None:
        rows.append({"name": "y", "status": "verified", "ground": "hyp", "value": y, "means": "y"})
    r = zfl.run({"rows": rows, "claim": claim})
    assert r.get("ok"), (value, claim, [i for i in r.get("issues", []) if i["level"] == "error"])
    return r["report"]["numeric"]["disposition"]


# 1. the gap decides, the closure does not ------------------------------------------------------------------------
PAIRS = [  # (open value, closed value, claim, verdict with the gap)
    ("(0,inf]", "[0,inf]", "x > 0", "EARNED"),
    ("(0,inf]", "[0,inf]", "x != 0", "EARNED"),
    ("(0,2]", "[0,2]", "ln(x) <= 1", "EARNED"),
    ("(0,inf]", "[0,inf]", "1/x > 0", "EARNED"),
    ("(0,inf]", "[0,inf]", "x**2 > 0", "EARNED"),
    ("(-1,1)", "[-1,1]", "x**2 < 1", "EARNED"),
    ("(-inf,0)", "(-inf,0]", "1/x < 0", "EARNED"),
    ("(0,inf]", "[0,inf]", "x <= 0", "REFUTED"),
    ("(0,inf]", "[0,inf]", "x == 0", "REFUTED"),
    ("(0,5]", "[0,5]", "x*y > 0", "EARNED"),
]
for op, cl, claim, want in PAIRS:
    y_open = op if "y" in claim else None
    got = verdict(op, claim, y=y_open)
    check(got == want, f"gap: {claim} over {op} -> {got}, want {want}")
    got_c = verdict(cl, claim, y=(cl if "y" in claim else None))
    check(got_c == "OPEN", f"closure: {claim} over {cl} -> {got_c}, want OPEN (else the gap did not decide)")

# an int with 0 < k reads from 1; an excluded lattice point gives way to the next one
check(verdict("(0,5]", "x >= 1", scale="int") == "EARNED", "int gap: 0 < k gives k >= 1")
check(verdict("[0,5]", "x >= 1", scale="int") == "OPEN", "int closure: k in [0,5] is not >= 1")
check(verdict("(0,5)", "x <= 4", scale="int") == "EARNED", "int gap at the top: k < 5 gives k <= 4")

# a domain wholly outside stays E — with the excluded end now counted
check(verdict("[-2,0)", "ln(x) <= 1") == "E", "ln over [-2,0) has no readings")
check(verdict("[-2,0)", "sqrt(x) >= 0") == "E", "sqrt over [-2,0) has no readings")
check(verdict("[-2,0]", "ln(x) <= 1") == "E", "ln over [-2,0]: no reading is positive (0 is not) -> E, as before")
check(verdict("[-2,1]", "ln(x) <= 1") == "OPEN", "ln over [-2,1]: some readings defined, some not -> a mark")

# an empty open interval is no reading at all
q, _ = parse_quantities("e=(1,1]")
check(q["e"]["no_readings"] is not None, "(1,1] is empty")

# 2. the other side: a forced verdict holds at every reading --------------------------------------------------------
OPS = {"<": lambda a, b: a < b, "<=": lambda a, b: a <= b, ">": lambda a, b: a > b, ">=": lambda a, b: a >= b,
       "==": lambda a, b: a == b, "!=": lambda a, b: a != b}


def _ev(e, env):
    if isinstance(e, Fraction):
        return e
    if isinstance(e, str):
        return env[e]
    op, a, b = e
    x, y = _ev(a, env), _ev(b, env)
    return {"add": x + y, "sub": x - y, "mul": x * y, "div": x / y}[op]


def _points(lo, hi, lo_open, hi_open, rnd):
    lo = Fraction(-50) if lo == "-inf" else Fraction(lo)
    hi = Fraction(50) if hi == "inf" else Fraction(hi)
    pts = [lo + (hi - lo) * Fraction(rnd.randint(1, 999), 1000) for _ in range(60)]
    pts += [lo + Fraction(1, 10 ** k) for k in range(1, 8)] + [hi - Fraction(1, 10 ** k) for k in range(1, 8)]
    if not lo_open:
        pts.append(lo)
    if not hi_open:
        pts.append(hi)
    return [p for p in pts if lo <= p <= hi]


def _box(v):
    lo, hi = v[1:-1].split(",")
    return lo, hi, v[0] == "(", v[-1] == ")"


rnd = random.Random(20261124)
ARITH = [  # claims the exact evaluator can read: + - * / and ** only
    ("(0,inf]", "x > 0"), ("(0,inf]", "1/x > 0"), ("(0,inf]", "x**2 > 0"), ("(-1,1)", "x**2 < 1"),
    ("(-inf,0)", "1/x < 0"), ("(0,inf]", "x != 0"), ("(0,inf]", "x == 0"), ("(0,3]", "x*x - 2*x + 1 >= 0"),
    ("(1,4)", "1/(x - 1) > 0"), ("(1,4)", "x**-2 < 1"), ("[2,3)", "x != 3"), ("(0,1)", "x**3 < x"),
]
for v, claim in ARITH:
    disp = verdict(v, claim)
    if disp not in ("EARNED", "REFUTED"):
        continue
    sign = next(s for s in ("!=", "<=", ">=", "==", "<", ">") if s in claim)
    left, right = claim.split(sign, 1)
    e1, e2 = _parse_arith(left, {"x": {}}), _parse_arith(right, {"x": {}})
    lo, hi, lo_o, hi_o = _box(v)
    bad = [p for p in _points(lo, hi, lo_o, hi_o, rnd)
           if OPS[sign](_ev(e1, {"x": p}), _ev(e2, {"x": p})) != (disp == "EARNED")]
    check(not bad, f"soundness: {claim} over {v} is {disp}, but x = {bad[:1]} disagrees")

# 3. the readers ----------------------------------------------------------------------------------------------------
check(_parse_arith("-x**2", {"x": {}}) == ("sub", Fraction(0), ("mul", "x", "x")), "-x**2 is -(x*x)")
check(_parse_arith("(x)**(2)", {"x": {}}) == ("mul", "x", "x"), "(x)**(2)")
check(_parse_arith("2*x**2", {"x": {}}) == ("mul", Fraction(2), ("mul", "x", "x")), "2*x**2")
check(_parse_arith("x**0", {"x": {}}) == Fraction(1), "x**0 is 1")
try:
    _parse_arith("x**y", {"x": {}, "y": {}})
    check(False, "x**y with a non-literal exponent must be refused")
except ValueError:
    pass
check(verdict("[1,inf]", "x != 0") == "EARNED" and verdict("[0,inf]", "x != 0") == "OPEN", "!= both sides")
check(verdict("[1,inf]", "x ≠ 0") == "EARNED", "≠ spelled out")

print(f"STRICT BOUND GREEN — {N[0]} checks" if not FAILS else f"test_znum_gap: {len(FAILS)} failures of {N[0]}")
sys.exit(1 if FAILS else 0)
