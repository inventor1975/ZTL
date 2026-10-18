# -*- coding: utf-8 -*-
"""
Stand: HC4 contraction (zcontract) — a box contracted by a constraint keeps EVERY point meeting it; EMPTY only when
none does. Checked against points, not against the code's own reading:
  1. the cases a reading loses: x*x - 2*x <= -2 on [0, 3] (reading [-6, 9]; least value -1) — EMPTY; <= -1 not;
     exp(x) + x >= 30 on [0, 3] — EMPTY; sqrt(x*x + 4*y) - x <= 0.1 on [1,2]x[1,3] — EMPTY;
  2. FUZZ: random expressions (+ - * / sqrt exp ln pow atan, repeated quantities), random boxes, random bounds;
     whenever a sampled point meets the constraint, the contracted box holds it, and an EMPTY verdict never meets
     a point (6000 cases x 300 points);
  3. MUTATION: a projection made too narrow (z = a + b narrowing a to z - b shrunk by 1 %) is caught by the fuzz.
Run:  python3 test_zcontract.py   -> ZCONTRACT GREEN
"""
import math
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import zcontract as K              # noqa: E402
from znumjudge import _parse_arith  # noqa: E402

ok = fail = 0


def check(cond, msg):
    global ok, fail
    if cond:
        ok += 1
        print("  ok  ", msg)
    else:
        fail += 1
        print("  FAIL", msg)


def parse(s, names):
    return _parse_arith(s, {n: {} for n in names})


# 1. the cases a reading loses
X03 = {"x": (F(0), F(3))}
check(K.contract(parse("x*x - 2*x", ["x"]), "<=", -2, X03) is None, "x*x - 2*x <= -2 on [0, 3]: EMPTY (least -1)")
check(K.contract(parse("x*x - 2*x", ["x"]), "<=", -1, X03) is not None, "x*x - 2*x <= -1 on [0, 3]: not empty (x = 1)")
check(K.contract(parse("exp(x) + x", ["x"]), ">=", 30, X03) is None, "exp(x) + x >= 30 on [0, 3]: EMPTY (max 23.09)")
check(K.contract(parse("sqrt(x*x + 4*y) - x", ["x", "y"]), "<=", F(1, 10), {"x": (F(1), F(2)), "y": (F(1), F(3))})
      is None, "sqrt(x*x + 4*y) - x <= 0.1 on [1,2]x[1,3]: EMPTY (least 0.83)")

# 2. fuzz
FN = {"sqrt": math.sqrt, "exp": math.exp, "ln": math.log, "atan": math.atan}


def gen(rng, names, depth):
    if depth == 0 or rng.random() < 0.25:
        return rng.choice(names) if rng.random() < 0.75 else str(rng.choice([1, 2, 3, F(1, 2), F(3, 2)]))
    k = rng.random()
    if k < 0.55:
        op = rng.choice(["+", "-", "*", "/"])
        return f"({gen(rng, names, depth - 1)} {op} {gen(rng, names, depth - 1)})"
    if k < 0.75:
        f = rng.choice(["sqrt", "exp", "ln", "atan"])
        inner = gen(rng, names, depth - 1)
        if f in ("sqrt", "ln"):
            inner = f"({inner})*({inner}) + 1"       # positive argument
        if f == "exp":
            inner = f"atan({inner})"                  # bounded argument
        return f"{f}({inner})"
    base = gen(rng, names, depth - 1)
    return f"pow(({base})*({base}) + 1, {rng.choice(['2', '3', '1/2', '3/2'])})"


def fval(text, pt):
    t = text.replace("pow(", "_pow(")
    return eval(t, {"__builtins__": {}, "_pow": lambda a, b: a ** b, **FN}, pt)


def run_fuzz(cases, points, seed):
    rng = random.Random(seed)
    bad_empty = bad_out = tried = empties = 0
    for _ in range(cases):
        names = ["x", "y"]
        text = gen(rng, names, 3)
        try:
            node = parse(text, names)
        except Exception:                             # noqa: BLE001 — a form the reader does not take
            continue
        dom = {}
        for n in names:
            a = F(rng.randint(-40, 40), 10)
            dom[n] = (a, a + F(rng.randint(1, 40), 10))
        pts = []
        for _p in range(points):
            pt = {n: rng.uniform(float(lo), float(hi)) for n, (lo, hi) in dom.items()}
            try:
                v = fval(text, pt)
            except (ZeroDivisionError, ValueError, OverflowError):
                continue
            pts.append((pt, v))
        if not pts:
            continue
        vs = sorted(v for _p, v in pts)
        b = F(vs[len(vs) // 2]).limit_denominator(10 ** 6) if rng.random() < 0.5 else \
            F(vs[0] - abs(vs[0]) * 0.1 - 0.5).limit_denominator(10 ** 6)
        op = rng.choice(["<=", ">="])
        try:
            got = K.contract(node, op, b, dom)
        except (ZeroDivisionError, OverflowError):
            continue
        tried += 1
        # met CLEARLY: a float value within 1e-7 (relative) of the bound is no witness (MEASURED 2026-10-19: a
        # constant 531442^(3/2) read 387421582.50051516 in floats, .50051440 exactly — below the bound, EMPTY right)
        tol = 1e-7 * max(1.0, abs(float(b)))
        meets = [(pt, v) for pt, v in pts if (v <= float(b) - tol if op == "<=" else v >= float(b) + tol)]
        if got is None:
            empties += 1
            if meets:
                bad_empty += 1
                print("    EMPTY but met:", text, op, b, dom, meets[0])
        else:
            for pt, _v in meets:
                if any(not (float(got[n][0]) - 1e-9 <= pt[n] <= float(got[n][1]) + 1e-9) for n in pt):
                    bad_out += 1
                    print("    point outside:", text, op, b, dom, got, pt)
                    break
    return tried, empties, bad_empty, bad_out


tried, empties, bad_empty, bad_out = run_fuzz(int(os.environ.get("ZC_CASES", 6000)), 300, 18)
check(tried > 0.6 * int(os.environ.get("ZC_CASES", 6000)) and empties > 0.04 * int(os.environ.get("ZC_CASES", 6000)) and bad_empty == 0 and bad_out == 0,
      f"fuzz: {tried} constraints, {empties} EMPTY — no EMPTY with a meeting point ({bad_empty}), no meeting point "
      f"outside a contracted box ({bad_out})")

# 3. mutation: a too-narrow projection must be caught
_orig = K._sub


def _narrow_sub(a, b):
    lo, hi = _orig(a, b)
    if isinstance(lo, float) or isinstance(hi, float):
        return lo, hi
    w = (hi - lo) / 100
    return lo + w, hi - w


K._sub = _narrow_sub
t2, e2, be2, bo2 = run_fuzz(int(os.environ.get("ZC_CASES", 6000)) // 2, 300, 7)
K._sub = _orig
check(be2 + bo2 > 0, f"mutation (z = a + b narrowed 1 %): caught — {be2} false EMPTY, {bo2} points outside")

# 4. the kernel's leaf (zmin): a FAILS leaf shown by contraction is accepted where the requirement is met nowhere on
# the piece — and only there; the plain reading of the same leaf cannot show it
import zmin as ZM                  # noqa: E402
_qs = {"x": {"lo": F(0), "hi": F(3)}}
_obj = parse("x", ["x"])
_row = parse("x*x - 2*x", ["x"])
_leaf = {"leaf": "fails", "row": 0, "at": {}, "cert": {"leaf": "hc4"}}
okA, _wA = ZM.check_lower_bound(_obj, _qs, [(_row, "<=", F(-2), _qs)], {"x": (F(0), F(3))}, F(0), _leaf)
okB, whyB = ZM.check_lower_bound(_obj, _qs, [(_row, "<=", F(-1), _qs)], {"x": (F(0), F(3))}, F(0), _leaf)
okC, _wC = ZM.check_lower_bound(_obj, _qs, [(_row, "<=", F(-2), _qs)], {"x": (F(0), F(3))}, F(0),
                                {"leaf": "fails", "row": 0, "at": {}, "bound": "-2", "cert": None})
check(okA and not okB and not okC, f"zmin: an hc4 leaf for x*x - 2*x <= -2 on [0, 3] ACCEPTED; for <= -1 (met at "
      f"x = 1) REFUSED ({whyB}); the plain reading of the same leaf cannot show it")

print(f"zcontract: {ok} ok, {fail} failed")
print("ZCONTRACT GREEN" if fail == 0 else "ZCONTRACT RED")
