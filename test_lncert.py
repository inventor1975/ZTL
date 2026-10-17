# -*- coding: utf-8 -*-
"""
Stand: the kernel's ln readings carry the witnesses of the Lean rule ZSlopeSqrt.VRead.ln (zero axioms): the low side L
has an ExpCert (ZExp) of e^L whose top is <= the argument's low end, the high side one whose bottom is >= its high end.
zfunc.iv_ln checks every reading IN THE RUN (zexpcert), moving a side outward by the first margin that certifies
(0, 2^-55, 2^-30, 2^-10); a side none certifies is counted in LN_UNCOVERED.
  1. 2000 random intervals in [10^-6, 10^6]: every side certified, how many needed a margin (2026-10-17: ln_pt's
     brackets are tighter than exp_pt's — 5955 of 6000 sides had no certificate before the margin);
  2. ln 10 (log10's divisor) certified;
  3. MUTATION: a low side above ln's true value by 1 is not rescued by any margin — counted, never silently passed.
Run:  python3 test_lncert.py   -> LNCERT GREEN
"""
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import zfunc                       # noqa: E402

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
zfunc.LN_UNCOVERED[0] = 0
moved = n = 0
for _ in range(2000):
    a = F(rng.randint(1, 10 ** 6), rng.randint(1, 10 ** 6)) * F(10) ** rng.randint(-1, 1)
    b = a + F(rng.randint(0, 10 ** 6), 10 ** 6)
    raw = zfunc._iv_mono(zfunc.ln_pt, (a, b), -zfunc.INF, zfunc.INF)
    r = zfunc.iv_ln((a, b))
    n += 2
    moved += (r[0] != raw[0]) + (r[1] != raw[1])
check(zfunc.LN_UNCOVERED[0] == 0, f"{n} sides of ln readings: all certified ({moved} moved outward by a margin)")
lo, hi = zfunc.LN10
check(zfunc._ln_side(F(10), F(lo), "lo") and zfunc._ln_side(F(10), F(hi), "hi"), "ln 10's bracket certified")
zfunc.LN_UNCOVERED[0] = 0
r = zfunc._cert_ln((F(3), F(4)), (zfunc.ln_pt(F(3))[0] + 1, zfunc.ln_pt(F(4))[1]))
check(zfunc.LN_UNCOVERED[0] == 1, "MUTATION: a low side 1 above ln 3 — no margin certifies it, counted")
print()
if fail:
    print(f"LNCERT RED ({fail} failed, {ok} ok)")
    sys.exit(1)
print(f"LNCERT GREEN ({ok} checks)")
