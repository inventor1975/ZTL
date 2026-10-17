# -*- coding: utf-8 -*-
"""
Stand: the kernel's Taylor coefficients (zcertify.taylor_coeffs) are covered by the Lean reading ZJetRead.CRead, whose
soundness (cread_sound) and closure (ZJetClose.cread_good) give the Taylor leaf of every even order
(ZJetClose.taylorN_kernel, zero axioms).

ztaylorcert mirrors CRead in exact rationals: each node's interval must contain the exact interval Lean's recurrence
builds from the kernel's own intervals of the children (convolutions with corners per term, the quotient through
[1/b0], exp and the coupled sin/cos through D_t = (t+1)·a_{t+1}, tan as sin/cos, Miller's combined weights).
  1. functions of the Lean grammar, at points and over pieces, orders 2..12: every kernel series passes
     (2026-10-17, ln, log10, real powers and atan added: the integral stand's 4153 series — 4029 covered, 0 failing
     an inequality; the rest: no series 124, all sqrt(x) at 0, refused);
  2. outside the grammar the reason is named, and it is not a fault;
  3. MUTATION: a coefficient of an inner node (×, ÷, exp, sin, cos, tan, power, +, √) moved inside its own interval to a
     point off the truth is caught as a FAULT naming that node — the rule is not vacuous;
  4. THE IN-RUN CHECK (zintegral): sqrt(x) at 0 has no series and no symbolic leaf either (the 124 "no series" of the
     integral stand, 2026-10-17: all sqrt(x) on [0, w], all refused — never a premise); a covered integrand's leaves
     have no fault; a kernel whose top coefficient is
     narrowed off the truth has its Taylor leaf refused.
Run:  python3 test_ztaylorcert.py   -> ZTAYLORCERT GREEN
"""
import os
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import zcertify as ZC              # noqa: E402
import zintegral as ZI             # noqa: E402
import ztaylorcert as T            # noqa: E402
from znumjudge import _parse_arith, parse_quantities   # noqa: E402

ok = fail = 0


def check(cond, msg):
    global ok, fail
    if cond:
        ok += 1
        print("  ok  ", msg)
    else:
        fail += 1
        print("  FAIL", msg)


def fs(v):
    return f"{v.numerator}/{v.denominator}"


def setup(t, boxes):
    qs = parse_quantities(", ".join(f"{n}=[{fs(a)},{fs(b)}] credit" for n, (a, b) in boxes.items()))[0]
    return _parse_arith(t, qs), qs


COVERED = ["exp(0 - x*x)", "exp(sin(x))", "1/(1 + x*x)", "tan(x/2)", "pow(x + 2, 5)", "cos(x)*exp(x)",
           "exp(x)/(2 + sin(x))", "sin(x*x) - cos(3*x)", "x*x*x - 2*x + 1", "exp(p*x)/(1 + p*x*x)", "tan(x)*sin(x)",
           "sqrt(x + 1)", "sqrt(1 + x*x)*exp(0 - x)", "1/sqrt(x + p)",
           "log10(x + 1)", "sin(x)*ln(x + 1)", "pow(x + 1, 3/2)/(1 + x*x)", "ln(1 + x*x)*exp(0 - x)",
           "atan(x*x)", "atan(1 + x)*exp(0 - x)"]
PIECES = [(F(1, 4), F(3, 8)), (F(5, 16), F(5, 16)), (F(0), F(1, 2)), (F(7, 8), F(7, 8)), (F(1, 3), F(1, 3) + F(1, 10 ** 6))]

print("1. the Lean grammar: every kernel series passes")
n_ok = n_all = 0
for t in COVERED:
    e, qs = setup(t, {"x": (F(0), F(1)), "p": (F(1, 2), F(1))})
    for u, v in PIECES:
        for n in (2, 4, 6, 8, 12):
            tr = {}
            cs = ZC.taylor_coeffs(e, "x", qs, {"x": (u, v)}, n, trace=tr)
            if cs is None:
                continue
            n_all += 1
            n_ok += T.check(e, "x", qs, {"x": (u, v)}, n, cs, tr)[0]
check(n_all > 450 and n_ok == n_all, f"{n_ok} of {n_all} series (20 functions x 5 pieces x orders 2..12) pass CRead")

print("2. outside the grammar: named, not a fault")
for t, want in (("ln(x - 1/2)", "no series"), ("pow(x - 2, 3)", "base not read >= 0")):
    e, qs = setup(t, {"x": (F(0), F(1))})
    tr = {}
    cs = ZC.taylor_coeffs(e, "x", qs, {"x": (F(1, 4), F(3, 8))}, 6, trace=tr)
    good, why, fault = T.check(e, "x", qs, {"x": (F(1, 4), F(3, 8))}, 6, cs, tr)
    check(not good and want in why and not fault, f"{t}: {why!r}, no fault")

print("3. MUTATION: an inner coefficient moved off the truth is a fault naming its node")


def mutate(t, node_op, k, piece=(F(1, 4), F(3, 8)), n=6):
    e, qs = setup(t, {"x": (F(0), F(1))})
    tr = {}
    cs = ZC.taylor_coeffs(e, "x", qs, {"x": piece}, n, trace=tr)
    good0 = T.check(e, "x", qs, {"x": piece}, n, cs, tr)[0]
    keys = [kk for kk in tr if isinstance(kk, tuple) and kk[0] == node_op and "x" in ZC._names(kk)]
    key = keys[0]
    s = list(tr[key])
    lo, hi = s[k]
    s[k] = (hi, hi)                       # a point at the top end: inside the kernel's own interval, off the truth
    tr2 = dict(tr)
    tr2[key] = s
    top = cs if key == e else tr2.get(e, cs)
    good, why, fault = T.check(e, "x", qs, {"x": piece}, n, top, tr2)
    return good0, good, why, fault


for t, op, k in (("exp(sin(x))*(1 + x)", "mul", 3), ("1/(1 + x*x)", "div", 2), ("exp(sin(x))", "exp", 4),
                 ("exp(sin(x))", "sin", 3), ("cos(x)*x", "cos", 2), ("tan(x/2)", "tan", 3),
                 ("pow(x + 2, 5)", "pow", 2), ("exp(x) + sin(x)", "add", 1), ("sqrt(x + 1)", "sqrt", 3),
                 ("atan(x*x)", "atan", 3)):
    good0, good, why, fault = mutate(t, op, k)
    check(good0 and not good and fault, f"{t}: {op} coefficient {k} moved -> fault {why!r}")

print("4. the in-run check (zintegral)")
ZI.TAYLOR_PREMISE.clear()
es, qss = setup("sqrt(x)", {"x": (F(0), F(1))})
cs_ = ZI.search(es, "x", F(0), F(1), qss, F(1, 10 ** 6))
check("gave_up" not in cs_ and "symbolic derivatives (no series)" not in ZI.TAYLOR_PREMISE,
      f"sqrt(x) on [0, 1]: the pieces at 0 have no series AND no symbolic leaf — refused, not a premise "
      f"({ZI.TAYLOR_PREMISE})")
e, qs = setup("exp(0 - x*x)", {"x": (F(0), F(1))})
ZI.TAYLOR_FAULT[0] = 0
c = ZI.search(e, "x", F(0), F(1), qs, F(1, 10 ** 12))
got = ZI.check(e, "x", 0, 1, qs, {"points": c["points"], "leaves": c["leaves"]})
check(got[0] and ZI.TAYLOR_FAULT[0] == 0 and any(isinstance(l, dict) and "taylor" in l for l in c["leaves"]),
      f"e^(-x^2) to 1e-12: {len(c['leaves'])} pieces, Taylor leaves, no fault")
orig = ZC.taylor_coeffs


def broken(expr, x, quantities, piece, n, trace=None):
    tr = {} if trace is None else trace
    cs = orig(expr, x, quantities, piece, n, trace=tr)
    if cs is None:
        return cs
    cs = list(cs)
    cs[n] = (cs[n][1], cs[n][1])          # the top coefficient narrowed to its upper end
    tr[expr] = cs
    return cs


ZC.taylor_coeffs = broken
try:
    r = ZI._piece_enclosure(e, "x", F(1, 4), F(3, 8), qs, {}, {"taylor": 6}, {})
finally:
    ZC.taylor_coeffs = orig
check(r[0] is None and "Lean reading" in r[1], f"a narrowed top coefficient: the leaf refused ({r[1]!r})")

print()
if fail:
    print(f"ZTAYLORCERT RED ({fail} failed, {ok} ok)")
    sys.exit(1)
print(f"ZTAYLORCERT GREEN ({ok} checks)")
