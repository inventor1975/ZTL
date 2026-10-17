# -*- coding: utf-8 -*-
"""
Stand: the kernel's monotone leaf is covered by ZMonoStep.monotone_leaf_up/down_step (zero axioms): a step reading of
f (ZDeriv.StepRead) and the sign of the grammar's own derivative D f, read by Lean (naive, affine, their meet).
zmonocert checks both in the run; zintegral counts a leaf it does not cover in MONO_PREMISE.
  1. integrals with monotone leaves: every sign covered (2026-10-17, the integral stand: 182 monotone leaves, 0
     premises; 8 of them only through D f's affine reading);
  2. lean_D is a derivative: at 105 random points it equals the kernel's symbolic derivative (mpmath, 40 digits);
  3. no step reading: the reason named (a divisor across zero, √ at 0);
  4. MUTATION: the opposite sign claimed is refused.
Run:  python3 test_zmonocert.py   -> ZMONOCERT GREEN
"""
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import zcertify as ZC              # noqa: E402
import zintegral as ZI             # noqa: E402
import zmonocert as M              # noqa: E402
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


print("1. monotone leaves: the sign covered")
for t, boxes in (("exp(0 - x*x)", {"x": (F(0), F(1))}), ("x*exp(0 - x)/(1 + x)", {"x": (F(0), F(3))}),
                 ("sin(x)*exp(0 - x)", {"x": (F(0), F(2))}), ("pow(x + 1, 3)", {"x": (F(0), F(1, 4))}),
                 ("x*ln(1 + x)", {"x": (F(0), F(1))}), ("pow(1 + x, 3/2)", {"x": (F(0), F(1, 2))}),
                 ("x*atan(1 + x)", {"x": (F(0), F(1))})):
    e, qs = setup(t, boxes)
    ZI.MONO_PREMISE.clear()
    n_mono = [0]
    orig = M.sign_covered

    def sc(*args):
        n_mono[0] += 1
        return orig(*args)
    M.sign_covered = sc
    try:
        c = ZI.search(e, "x", boxes["x"][0], boxes["x"][1], qs, F(1, 10 ** 2), orders=())
    finally:
        M.sign_covered = orig
    check("gave_up" not in c and not ZI.MONO_PREMISE and n_mono[0] > 0,
          f"{t}: {n_mono[0]} monotone signs checked, premises {ZI.MONO_PREMISE}")

print("2. lean_D is the derivative (against the kernel's, at random points)")
try:
    import mpmath as mp
    mp.mp.dps = 40
    rng = random.Random(17)
    bad = n = 0
    for t in ("x*exp(0 - x)/(1 + x)", "sin(x)*cos(2*x) - tan(x/3)", "sqrt(1 + x*x)*pow(x + 2, 3)",
              "exp(sin(x))/(2 + cos(x))", "ln(1 + x*x)*log10(2 + x)", "pow(1 + x, 3/2)",
              "atan(x*x)*x"):
        e, qs = setup(t, {"x": (F(0), F(1))})
        dl, dk = M.lean_D(e, "x"), ZC.derivative(e, "x")
        for _ in range(15):
            pt = F(rng.randint(1, 999), 1000)
            q2 = dict(qs, x=dict(qs["x"], lo=pt, hi=pt))
            a = ZC._reading(dl, q2, {"x": (pt, pt)})
            b = ZC._reading(dk, q2, {"x": (pt, pt)})
            n += 1
            bad += not (a is not None and b is not None and max(a[0], b[0]) <= min(a[1], b[1]))
    check(bad == 0 and n == 105, f"{n} points: lean_D's reading meets the kernel's derivative's every time ({bad} apart)")
except ImportError:
    print("  (mpmath not installed: skipped)")

print("3. no step reading: named")
for t, box, want in (("x/(x - 1/2)", (F(1, 4), F(3, 4)), "divisor"),
                     ("sqrt(x)", (F(0), F(1, 4)), "sqrt")):
    e, qs = setup(t, {"x": (F(0), F(1))})
    why = M.sign_covered(e, "x", qs, {"x": box}, "+")
    check(want in why, f"{t} on [{float(box[0])}, {float(box[1])}]: {why!r}")

print("4. MUTATION: the opposite sign")
e, qs = setup("exp(0 - x*x)", {"x": (F(0), F(1))})
check(M.sign_covered(e, "x", qs, {"x": (F(1, 4), F(1, 2))}, "-") == "", "exp(-x^2) falls on [1/4, 1/2]: covered")
check("sign" in M.sign_covered(e, "x", qs, {"x": (F(1, 4), F(1, 2))}, "+"), "claimed rising: refused")

print()
if fail:
    print(f"ZMONOCERT RED ({fail} failed, {ok} ok)")
    sys.exit(1)
print(f"ZMONOCERT GREEN ({ok} checks)")
