# -*- coding: utf-8 -*-
"""
Stand: the kernel's sin/cos over intervals are covered by the Lean theorems ZTrig.Ev_cos / ZTrig.Ev_sin.

zfunc.iv_cos / iv_sin bound sin and cos over [a0, a1] by the ends' brackets, and by +-1 where an extremum may lie
inside (pi itself a bracket, zfunc.PI). The Lean rule (ZTrig10/11, zero axioms) takes, for each side: either the
+-1, or partial-sum certificates at both ends (CosCert/SinCert: C_M(x) +- 2·|x|^M/M!, M good) PLUS whole-period
shifts p, q and a margin 2^-B placing the window where no extremum is (CosHi/CosLo/SinHi/SinLo), with pi's
bracket checked by cos at its halves (PiBr). This stand mirrors those definitions in exact rationals and checks:
  1. pi's bracket: cos(PI0/2) > 0 and cos(PI1/2) < 0 are certified (PiBr);
  2. seeded windows in [-25, 25] of widths 1e-6 .. 5, plus windows ending 1e-3 / 1e-5 short of every extremum
     k·pi/2, |k| <= 8: for every side the kernel returns, the Lean witnesses exist — the theorems cover what the
     kernel outputs (2026-10-17: 13 952 sides measured over 16 seeds, 0 without witnesses);
  3. MUTATION: a top moved below the true value at an end, and a window that holds an extremum, are refused —
     the rule is not vacuous;
  4. tan (ZTrig14.TanVal): the kernel's iv_tan readings have their witnesses; a bottom above the truth is refused;
  5. THE IN-RUN CHECK (zfunc._covered + ztrigcert, 2026-10-17): no reading needed widening; a kernel bracket
     shifted off the truth is widened to +-1 (tan: no reading) and counted — never sent out uncovered.
Run:  python3 test_trigcert.py   -> TRIGCERT GREEN
"""
import math
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import zfunc                       # noqa: E402

ok = fail = 0


def check(name, cond, why=""):
    global ok, fail
    if cond:
        ok += 1; print(f"  OK   {name}")
    else:
        fail += 1; print(f"  FAIL {name} — {why}")


def series(x, M):
    """ZTrig.Cn / Sn: the partial sums of cr / ci (crci: (m+1)·cr_{m+1} = −x·ci_m, (m+1)·ci_{m+1} = x·cr_m)."""
    cr, ci, C, S = F(1), F(0), F(0), F(0)
    for m in range(M):
        C += cr; S += ci
        cr, ci = (-ci) * x / (m + 1), cr * x / (m + 1)
    return C, S


def tm(a, M):
    t = F(1)
    for k in range(M):
        t = t * a / (k + 1)
    return t


def cert(x, which, need_lo=None, need_hi=None, Mmax=600):
    """A CosCert / SinCert at x (a = |x|, Good a M: 2a <= M + 1) with lo >= need_lo and hi <= need_hi."""
    a = abs(x)
    M = 1
    while 2 * a > M + 1:
        M += 1
    while M <= Mmax:
        C, S = series(x, M)
        v = C if which == "cos" else S
        t = 2 * tm(a, M)
        if (need_lo is None or need_lo <= v - t) and (need_hi is None or v + t <= need_hi):
            return M
        M += max(1, M // 4)
    return None


RL, RH = F(zfunc.PI[0]) / 2, F(zfunc.PI[1]) / 2


def window(kind, lu, hu):
    """p, q, B for the side's no-extremum window — the exact inequalities of CosHi/CosLo/SinHi/SinLo."""
    j0 = math.floor(float(lu) / (2 * math.pi))
    for j in range(j0 - 2, j0 + 3):
        p, q = (j, 0) if j >= 0 else (0, -j)
        for B in range(1, 400, 3):
            e = F(1, 2 ** B)
            if kind == "cosHi":
                c1 = 4 * p * RH + 4 * e <= lu + 4 * q * RL
                c2 = hu + 4 * q * RH + 8 * e <= 4 * p * RL + 4 * RL
            elif kind == "cosLo":
                c1 = 4 * p * RH + 6 * e <= lu + 4 * q * RL + 2 * RL
                c2 = hu + 4 * q * RH + 6 * e <= 4 * p * RL + 2 * RL
            elif kind == "sinHi":
                c1 = 4 * p * RH + 7 * e <= lu + 4 * q * RL + 3 * RL
                c2 = hu + 4 * q * RH + 5 * e <= 4 * p * RL + RL
            else:
                c1 = 4 * p * RH + 5 * e <= lu + 4 * q * RL + RL
                c2 = hu + 4 * q * RH + 7 * e <= 4 * p * RL + 3 * RL
            if c1 and c2:
                return p, q, B
    return None


def sides(which, lu, hu, lo, hi):
    """Lean witnesses for the kernel's [lo, hi] over [lu, hu]: 'pm1', 'ok' or 'FAIL'."""
    out = []
    if hi >= 1:
        out.append("pm1")
    else:
        good = window(which + "Hi", lu, hu) and cert(lu, which, need_hi=hi) and cert(hu, which, need_hi=hi)
        out.append("ok" if good else "FAIL")
    if lo <= -1:
        out.append("pm1")
    else:
        good = window(which + "Lo", lu, hu) and cert(lu, which, need_lo=lo) and cert(hu, which, need_lo=lo)
        out.append("ok" if good else "FAIL")
    return out


def dyad(v, bits=20):
    return F(round(v * 2 ** bits), 2 ** bits)


check("pi's bracket certified by cos at its halves: cos(PI0/2) > 0, cos(PI1/2) < 0 (PiBr)",
      cert(RL, "cos", need_lo=F(1, 10 ** 200)) is not None and cert(RH, "cos", need_hi=F(-1, 10 ** 200)) is not None)

rnd = random.Random(20261017)
cases = []
for _ in range(150):
    c = rnd.uniform(-25, 25); w = rnd.choice([1e-6, 1e-3, 0.1, 0.5, 1.0, 2.0, 3.0, 5.0])
    cases.append((dyad(c - w / 2), dyad(c + w / 2)))
for k in range(-8, 9):
    e = k * math.pi / 2
    for d in (1e-3, 1e-5):
        cases.append((dyad(e - 0.5, 30), dyad(e - d, 30)))
        cases.append((dyad(e + d, 30), dyad(e + 0.5, 30)))
tally = {"ok": 0, "pm1": 0, "FAIL": 0}
bad = []
for lu, hu in cases:
    for which, iv in (("cos", zfunc.iv_cos), ("sin", zfunc.iv_sin)):
        lo, hi = (F(v) for v in iv((lu, hu)))
        for s in sides(which, lu, hu, lo, hi):
            tally[s] += 1
            if s == "FAIL":
                bad.append((which, float(lu), float(hu)))
n = sum(tally.values())
check(f"{n} kernel sides over {len(cases)} windows (cos and sin): every one has its Lean witnesses "
      f"({tally['ok']} by certified ends, {tally['pm1']} by +-1)", tally["FAIL"] == 0, bad[:3])

# MUTATIONS
refused, missed = 0, []
for lu, hu in cases[:60]:
    for which, iv in (("cos", zfunc.iv_cos), ("sin", zfunc.iv_sin)):
        v = math.cos(float(lu)) if which == "cos" else math.sin(float(lu))
        low_hi = F(v) - F(1, 1000)            # a top below the true value at lu
        if cert(lu, which, need_hi=low_hi, Mmax=200) is None:
            refused += 1
        else:
            missed.append((which, float(lu)))
check(f"{refused + len(missed)} tops moved 1e-3 below the true value at an end: every one refused",
      not missed, missed[:3])
holds = [("cosHi", F(-1, 10), F(1, 10)), ("cosLo", F(3), F(13, 4)), ("sinHi", F(3, 2), F(8, 5)),
         ("sinLo", F(-8, 5), F(-3, 2)), ("cosHi", F(62, 10), F(64, 10)), ("cosLo", F(-32, 10), F(-31, 10))]
check(f"{len(holds)} windows holding an extremum (0, pi, pi/2, -pi/2, 2pi, -pi): no no-extremum witness",
      all(window(k, a, b) is None for k, a, b in holds), [(k, float(a)) for k, a, b in holds if window(k, a, b)])

# TAN (ZTrig14.TanVal): the kernel's iv_tan over windows in [-1.5, 1.5]; ends rounded outward (q0, q1)


def tan_end(q, T, low, Mmax=400):
    """Certified sin/cos brackets at q with c_lo > 0 and T·c ≤ s_lo at both c ends (low) / s_hi ≤ T·c (high)."""
    a = abs(q)
    M = 1
    while 2 * a > M + 1:
        M += 1
    while M <= Mmax:
        C, S = series(q, M)
        t = 2 * tm(a, M)
        cl, ch, sl, sh = C - t, C + t, S - t, S + t
        if cl > 0 and ((low and T * cl <= sl and T * ch <= sl) or (not low and sh <= T * cl and sh <= T * ch)):
            return M
        M += max(1, M // 4)
    return None


def tanval(lu, hu, Tl, Th):
    q0, q1 = zfunc._down(lu), zfunc._up(hu)
    c0 = min(math.cos(float(q0)), math.cos(float(q1))) / 2
    if c0 <= 0:
        return "cos window"
    c0 = F(c0)
    if not (window("cosLo", q0, q1) and cert(q0, "cos", need_lo=c0) and cert(q1, "cos", need_lo=c0)):
        return "cos window"
    d = q1 - q0
    if not (window("sinLo", F(0), d) and cert(F(0), "sin", need_lo=F(0)) and cert(d, "sin", need_lo=F(0))):
        return "sin window"
    if tan_end(q0, Tl, True) is None:
        return "low end"
    if tan_end(q1, Th, False) is None:
        return "high end"
    return "ok"


tcases = []
for _ in range(120):
    c = rnd.uniform(-1.45, 1.45); w = rnd.choice([1e-6, 1e-3, 0.05, 0.3, 1.0])
    lo_, hi_ = max(-1.5, c - w / 2), min(1.5, c + w / 2)
    tcases.append((dyad(lo_), dyad(hi_)))
tcases += [(F(-3, 2), F(3, 2)), (F(0), F(0)), (F(3, 2), F(3, 2)), (F(-3, 2), F(-3, 2))]
tbad = [(float(a), float(b), r) for a, b in tcases
        for r in [tanval(a, b, *(F(v) for v in zfunc.iv_tan((a, b))))] if r != "ok"]
check(f"{len(tcases)} kernel tan readings over windows in [-1.5, 1.5] (incl. the edges): every one has its Lean "
      f"witnesses (ZTrig14.TanVal)", not tbad, tbad[:3])
tmiss = []
for a, b in tcases[:40]:
    Tl, Th = (F(v) for v in zfunc.iv_tan((a, b)))
    q0 = zfunc._down(a)
    if tan_end(q0, F(math.tan(float(q0))) + F(1, 1000), True, Mmax=200) is not None:
        tmiss.append(float(a))
check("40 tan bottoms moved 1e-3 above the true tan at the end: every one refused", not tmiss, tmiss[:3])

# THE IN-RUN CHECK (zfunc._covered, ztrigcert): every reading above was checked before it left; none was widened
check(f"in-run check: no sin/cos/tan reading of this stand needed widening (zfunc.TRIG_UNCOVERED = "
      f"{dict(zfunc.TRIG_UNCOVERED)})", all(v == 0 for v in zfunc.TRIG_UNCOVERED.values()))

# MUTATION OF THE KERNEL: a cos_pt / tan_pt bracket shifted off the truth must not leave uncovered
orig_cos, orig_tan = zfunc.cos_pt, zfunc.tan_pt
zfunc.cos_pt = lambda x: tuple(v - F(1, 100) for v in orig_cos(x))
before = zfunc.TRIG_UNCOVERED["cos"]
r = zfunc.iv_cos((F(1, 2), F(1)))
zfunc.cos_pt = orig_cos
check(f"a kernel cos bracket shifted 0.01 below the truth over [0.5, 1]: the top is widened to 1, counted "
      f"(got hi = {float(r[1])})", r[1] == 1 and zfunc.TRIG_UNCOVERED["cos"] > before)
zfunc.tan_pt = lambda x: tuple(v + F(1, 100) for v in orig_tan(x))
before = zfunc.TRIG_UNCOVERED["tan"]
r = zfunc.iv_tan((F(1, 2), F(1)))
zfunc.tan_pt = orig_tan
check("a kernel tan bracket shifted 0.01 above the truth over [0.5, 1]: no reading (a mark), counted",
      r is None and zfunc.TRIG_UNCOVERED["tan"] > before)
r = zfunc.iv_cos((F(1, 2), F(1)))
check("after the mutations are undone, the same reading is covered again (not widened)", r[1] < 1 and r[0] > -1)

print(f"\n{ok} ok, {fail} fail")
print("TRIGCERT GREEN" if fail == 0 else "TRIGCERT RED")
sys.exit(1 if fail else 0)
