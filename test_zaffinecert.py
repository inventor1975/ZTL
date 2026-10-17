# -*- coding: utf-8 -*-
"""
Stand: the kernel's AFFINE value readings are covered by the Lean theorem ZAffine.aff_sound (lean/ZAffine.lean,
ZAffine2.lean, zero axioms): zaffinecert replays zaffine.read with the kernel's own steps and checks each step's AffR
premises in exact rationals; zintegral checks every value reading of its interval and monotone leaves against Lean's
reading (the naive VRead, the affine AffR, their meet — ZAffine.boxEv_meet).
  1. the readings of the integral stand: every one covered (2026-10-17: 761 readings, 637 by the naive reading alone,
     124 only through the affine one — the red team's F1, closed);
  2. the replay IS the kernel: random expressions of + − × ÷ exp over random pieces, the replayed interval equals
     zaffine.read's (a mismatch would raise FAULT);
  3. MUTATION: a kernel reading shrunk past Lean's is named; an exp slope above e^a's certified lower bracket, a 1/x
     slope on the wrong side, and a rounding that drops its error are each caught as a failed premise;
  4. outside AffR the reason is named (sqrt, atan; 1/x of a negative interval).
Run:  python3 test_zaffinecert.py   -> ZAFFINECERT GREEN
"""
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import zaffine as ZA               # noqa: E402
import zaffinecert as AC           # noqa: E402
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


def replay(e, qs, piece):
    q2 = dict(qs)
    for n_, (lo, hi) in piece.items():
        q2[n_] = dict(qs[n_], lo=lo, hi=hi)
    return AC.read_checked(e, qs, piece, ZC._rat_sqrt, lambda n: ZC._plain(n, q2), lambda n: T._naive(n, qs, piece))


print("1. integrals whose readings need the affine form: every value reading covered")
cases = [("exp(0 - k*x)/(1 + k*x)", {"x": (F(0), F(2)), "k": (F(1, 2), F(1))}),
         ("x*exp(0 - x)/(1 + x)", {"x": (F(0), F(3))}),
         ("(exp(0 - x) - exp(0 - 2*x))/(1 + x*x)", {"x": (F(0), F(2))}),
         ("x*ln(1 + x)/(2 + x)", {"x": (F(0), F(2))}), ("pow(1 + x, 3/2)*exp(0 - x)", {"x": (F(0), F(2))})]
total_aff = 0
for t, boxes in cases:
    e, qs = setup(t, boxes)
    ZI.VALUE_PREMISE.clear()
    need = [0, 0]
    orig = AC.lean_covered

    def lc(f, qs_, piece, r):
        w = orig(f, qs_, piece, r)
        nv = T._naive(f, qs_, piece)
        need[0] += 1
        need[1] += (w == "" and not (nv is not None and r[0] <= nv[0] and nv[1] <= r[1]))
        return w
    AC.lean_covered = lc
    try:
        c = ZI.search(e, "x", boxes["x"][0], boxes["x"][1], qs, F(1, 10 ** 4))
    finally:
        AC.lean_covered = orig
    total_aff += need[1]
    check("gave_up" not in c and not ZI.VALUE_PREMISE,
          f"{t}: {need[0]} value readings, {need[1]} of them only through the affine form; premises {ZI.VALUE_PREMISE}")
check(total_aff > 0, f"{total_aff} readings covered only through the affine form (the check is not idle)")

print("2. the replay is the kernel (random + − × ÷ exp, random pieces)")
rng = random.Random(20261017)


def rand_expr(d):
    if d == 0 or rng.random() < 0.25:
        return rng.choice(["x", "y", F(rng.randint(1, 5), rng.randint(1, 3))])
    op = rng.choice(["add", "sub", "mul", "div", "exp"])
    if op == "exp":
        return ("exp", ("mul", F(-1, rng.randint(1, 3)), rand_expr(d - 1)))
    if op == "div":
        return ("div", rand_expr(d - 1), ("add", F(1), ("mul", rand_expr(d - 1), rand_expr(d - 1))))
    return (op, rand_expr(d - 1), rand_expr(d - 1))


_, qx = setup("x + y", {"x": (F(-1), F(2)), "y": (F(0), F(1))})
n_run = n_cov = 0
for _ in range(400):
    e = rand_expr(3)
    a = F(rng.randint(-8, 15), 8)
    w = F(1, 2 ** rng.randint(1, 6))
    piece = {"x": (a, a + w), "y": (F(1, 4), F(3, 4))}
    try:
        iv, why = replay(e, qx, piece)
    except RuntimeError as ex:
        check(False, f"FAULT on {e}: {ex}")
        break
    n_run += 1
    n_cov += iv is not None
check(n_run == 400 and n_cov > 200, f"{n_run} random readings replayed, none lost the kernel; {n_cov} fully in AffR")

print("3. MUTATION")
e, qs = setup("exp(0 - k*x)/(1 + k*x)", {"x": (F(0), F(2)), "k": (F(1, 2), F(1))})
piece = {"x": (F(1, 2), F(1)), "k": (F(1, 2), F(1))}
r = ZC._reading(e, qs, piece)
check(AC.lean_covered(e, qs, piece, r) == "", "the kernel's reading itself is covered")
q = (r[1] - r[0]) / 4
check("tighter" in AC.lean_covered(e, qs, piece, (r[0] + q, r[1] - q)), "a kernel reading shrunk past Lean's is named")
keep = ZA._down
ZA._down = lambda x: keep(x) + F(1, 10 ** 6)          # every slope rounded UP: exp's slope above its lower bracket
try:
    _, why = replay(("exp", ("mul", F(-1), "x")), qs, {"x": (F(0), F(1))})
finally:
    ZA._down = keep
check("exp" in why, f"an exp slope above e^a's certified bracket is caught: {why!r}")
keepu = ZA._up
ZA._up = lambda x: keepu(x) - F(1, 10 ** 3)           # the 1/x slope (end b) and its deltas rounded DOWN
try:
    _, why = replay(("div", 1, ("add", 1, "x")), qs, {"x": (F(0), F(1, 64))})
finally:
    ZA._up = keepu
check(why != "", f"a 1/x min-range with its ends rounded inward is caught: {why!r}")
keep_tidy = ZA.Aff.tidy


def bad_tidy(self):
    keep_tidy(self)
    self.e = self.e / 2                                 # a rounding that drops half its error
    return self


ZA.Aff.tidy = bad_tidy
try:
    _, why = replay(("mul", ("exp", ("mul", F(-1), "x")), "x"), qs, {"x": (F(0), F(1))})
finally:
    ZA.Aff.tidy = keep_tidy
check("rounding" in why, f"a rounding that drops its error is caught: {why!r}")

print("4. outside AffR: named")
for t, boxes, want in (("x*sqrt(1 + x)", {"x": (F(0), F(1))}, "sqrt"), ("x*atan(1 + x)", {"x": (F(0), F(1))}, "atan"),
                       ("x/(x - 3)", {"x": (F(0), F(1))}, "negative")):
    e, qs = setup(t, boxes)
    _, why = replay(e, qs, {"x": (F(1, 4), F(1, 2))})
    check(want in why, f"{t}: {why!r}")

print()
if fail:
    print(f"ZAFFINECERT RED ({fail} failed, {ok} ok)")
    sys.exit(1)
print(f"ZAFFINECERT GREEN ({ok} checks)")
