# -*- coding: utf-8 -*-
"""
Stand: the kernel's atan readings are Lean's (lean/ZAtan, ZAtanCert, ZAffineAtan; zero axioms), and the run ENFORCES it.
Lean's atan is the grid sum of 1/(1 + t²); VRead.atan takes atan at the ends of its argument's reading as facts about
two rational points, certified by a Taylor chain from atan 0 = 0 (zatancert). zfunc.iv_atan moves a side outward by the
first margin the chain certifies (0, 2^-55, 2^-30, 2^-10); a side none certifies counts in ATAN_UNCOVERED, and a
reading during which that counter rises is NO Lean reading (ztaylorcert._val) — a premise, never silently covered.
  1. the chain against mpmath (60 digits): random points, integers to 10^6, dyadics, near 1e12; all brackets hold;
  2. 300 random intervals: every side certified (ATAN_UNCOVERED 0);
  3. MUTATION (red team F2, 2026-10-17): atan_pt shifted up by 2^-6 — the leaves' readings become premises
     (TAYLOR/VALUE_PREMISE), none passes as covered;
  4. an unbounded argument (red team F1): atan(p), sin(p), cos(p) with p = ? are no Lean reading — premises;
  5. atan of 1e12 and 1e30 reads (red team F3: a float underflow crashed it);
  6. the affine atan of a point a = b > 0 is in AffR (red team F4: a tie rounded its slope past psi(b));
  7. the chain's series refuses 1 + u·u not clear of zero (red team F5).
Run:  python3 test_atancert.py   -> ATANCERT GREEN
"""
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import zfunc as ZF                 # noqa: E402
import zatancert as A              # noqa: E402
import zintegral as ZI             # noqa: E402
import ztaylorcert as T            # noqa: E402
import zaffine as ZA               # noqa: E402
import zaffinecert as AC           # noqa: E402
import zcertify as ZC              # noqa: E402
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


rng = random.Random(20261017)
print("1. the chain holds the true atan")
try:
    import mpmath as mp
    mp.mp.dps = 60
    q = lambda f: mp.mpf(f.numerator) / f.denominator
    pts = [F(rng.randint(-10 ** 6, 10 ** 6), rng.randint(1, 10 ** 4)) for _ in range(120)]
    pts += [F(rng.randint(-10 ** 6, 10 ** 6)) for _ in range(20)] + [F(rng.randint(-2 ** 40, 2 ** 40), 2 ** 37) for _ in range(20)]
    pts += [F(10 ** 12) + F(1, 3), F(-10 ** 12)]
    bad = 0
    worst = 0
    for x in pts:
        L, H = A.atan_cert(x)
        tr = mp.atan(q(x))
        bad += not (q(L) <= tr <= q(H))
        worst = max(worst, float(q(H - L)))
    check(bad == 0, f"{len(pts)} points: the true atan inside every bracket (widest {worst:.1e})")
except ImportError:
    print("  (mpmath not installed: skipped)")

print("2. the kernel's readings certified")
ZF.ATAN_UNCOVERED[0] = 0
for _ in range(300):
    a = F(rng.randint(-4000, 4000), rng.choice([1, 8, 64, 1024, 3]))
    ZF.iv_atan((a, a + F(rng.randint(0, 100), 64)))
check(ZF.ATAN_UNCOVERED[0] == 0, f"300 random intervals: every side certified (ATAN_UNCOVERED {ZF.ATAN_UNCOVERED[0]})")


def setup(t, text):
    qs = parse_quantities(text)[0]
    return _parse_arith(t, qs), qs


def leaves(f, qs, leaf):
    ZI.TAYLOR_PREMISE.clear(); ZI.VALUE_PREMISE.clear(); ZI.MONO_PREMISE.clear(); ZI.TAYLOR_FAULT[0] = 0
    got = ZI.check(f, "x", F(0), F(1), qs, {"points": [f"{i}/4" for i in range(5)], "leaves": [leaf] * 4})
    return got[0], dict(ZI.TAYLOR_PREMISE), dict(ZI.VALUE_PREMISE)


print("3. MUTATION: an uncertified bracket is a premise, not covered")
f, qs = setup("atan(1/2 + x/4)*exp(0 - x)", "x=[0/1,1/1] credit")
acc0, tp0, vp0 = leaves(f, qs, {"taylor": 4})
check(acc0 and not tp0 and not vp0, f"atan(1/2 + x/4)·e^-x: the Taylor leaves covered (premises {tp0} {vp0})")
keep = ZF.atan_pt
ZF.atan_pt = lambda x: tuple(v + F(1, 64) for v in keep(x))
A._CACHE.clear(); A._CACHE[F(0)] = (F(0), F(0)); A._KEYS[:] = [F(0)]
try:
    for leaf in ({"taylor": 4}, "interval"):
        acc, tp, vp = leaves(f, qs, leaf)
        check(bool(tp) or bool(vp), f"atan_pt shifted by 2^-6, {leaf} leaves: premises {tp} {vp}")
finally:
    ZF.atan_pt = keep

print("4. an unbounded argument: no Lean reading")
for t in ("x*atan(p)", "x*sin(p)", "x*cos(p)"):
    f, qs = setup(t, "x=[0/1,1/1] credit, p=? credit")
    nv = T._naive(f, qs, {"x": (F(1, 4), F(1, 2))})
    acc, tp, vp = leaves(f, qs, "interval")
    check(nv is None and vp, f"{t}, p = ?: naive {nv}, premises {vp}")

print("5. huge arguments read")
ZF.ATAN_UNCOVERED[0] = 0
for x in (F(10 ** 12), F(10 ** 30)):
    try:
        r = ZF.iv_atan((x, x + 1))
        check(r[0] < r[1] and ZF.ATAN_UNCOVERED[0] == 0, f"atan of [{float(x):.0e}, +1]: [{float(r[0])}, {float(r[1])}]")
    except Exception as ex:
        check(False, f"atan of {float(x):.0e}: {type(ex).__name__} {ex}")

print("6. the affine atan of a point")
for v in (F(3), F(1, 3), F(-1, 3), F(0)):
    f, qs = setup("atan(p)", f"x=[0/1,1/1] credit, p=[{v.numerator}/{v.denominator},{v.numerator}/{v.denominator}] credit")
    q2 = dict(qs)
    iv, why = AC.read_checked(f, qs, {}, ZC._rat_sqrt, lambda n: ZC._plain(n, q2), lambda n: T._naive(n, qs, {}))
    check(iv is not None, f"atan(p), p = {v}: affine reading {iv and [float(iv[0]), float(iv[1])]} {why!r}")

print("7. the series refuses 1 + u·u across zero")
try:
    A.series(F(-3), F(2), 4)
    check(False, "a box [-3, 2]: no refusal")
except ValueError as ex:
    check("RecipOK" in str(ex), f"a box [-3, 2]: {ex}")

print()
if fail:
    print(f"ATANCERT RED ({fail} failed, {ok} ok)")
    sys.exit(1)
print(f"ATANCERT GREEN ({ok} checks)")
