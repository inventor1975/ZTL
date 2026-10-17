# -*- coding: utf-8 -*-
"""The Lean witnesses for the kernel's sin / cos / tan readings (lean/ZTrig10.lean, ZTrig11, ZTrig14), in exact
fractions — the bridge between zfunc.iv_cos / iv_sin / iv_tan and the theorems ZTrig.Ev_cos / Ev_sin / Ev_tan
(zero axioms, on VR's operational reals).

A side of a reading is covered by the theorem when it is +-1, or when its Lean witnesses exist:
  * CosCert / SinCert at both ends — a partial sum of the series with its tail, C_M(x) -+ 2·|x|^M/M!, M good
    (2|x| <= M + 1), the bracket inside the side;
  * PiBr — pi's bracket (zfunc.PI) checked by cos at its halves: cos(PI0/2) > 0, cos(PI1/2) < 0;
  * whole periods p, q and a margin 2^-B placing the window where no extremum is: the exact inequalities of
    ZTrig.CosHi / CosLo / SinHi / SinLo.
tan (ZTrig.TanVal): the ends rounded outward as the kernel does, cos > 0 over the window, sin >= 0 on [0, q1 - q0],
and at each end certified sin, cos brackets with Tl·c <= s (resp. s <= Th·c) at both ends of c's bracket.

The kernel computes by argument reduction and its own series (zfunc._sc_pt); the theorems are about the plain
partial sums. A reading that passes here is covered, however the kernel computed it. zfunc calls these on every
reading: a side without witnesses is widened to +-1 (tan: no reading) — never sent out uncovered.
"""
import math
from fractions import Fraction as F

import zfunc

MMAX = 2000


def cert(x, which, need_lo=None, need_hi=None):
    """The index M of a CosCert / SinCert at x whose bracket meets the needs (lo >= need_lo, hi <= need_hi),
    or None. The partial sums run incrementally; once M is good the bracket contains the true value, so a need
    beyond the current bracket's far side can never be met (stop)."""
    x = F(x)
    a = abs(x)
    cr, ci, C, S, t = F(1), F(0), F(0), F(0), F(1)     # cr_m, ci_m, C_m, S_m, a^m/m!
    for m in range(MMAX + 1):
        if 2 * a <= m + 1:
            v = C if which == "cos" else S
            lo, hi = v - 2 * t, v + 2 * t
            if (need_lo is None or need_lo <= lo) and (need_hi is None or hi <= need_hi):
                return m
            if (need_lo is not None and need_lo > hi) or (need_hi is not None and need_hi < lo):
                return None
        C += cr; S += ci
        cr, ci = (-ci) * x / (m + 1), cr * x / (m + 1)
        t = t * a / (m + 1)
    return None


RL, RH = F(zfunc.PI[0]) / 2, F(zfunc.PI[1]) / 2
_PIBR = None


def pibr():
    """PiBr: cos(PI0/2) > 0 and cos(PI1/2) < 0, certified (once)."""
    global _PIBR
    if _PIBR is None:
        _PIBR = (cert(RL, "cos", need_lo=F(1, 10 ** 300)) is not None and
                 cert(RH, "cos", need_hi=F(-1, 10 ** 300)) is not None)
    return _PIBR


# the window inequalities as  base1 + k1·e <= rhs1,  base2 + k2·e <= rhs2  (e = 2^-B), per kind
def _ineq(kind, p, q, lu, hu):
    if kind == "cosHi":
        return (4 * p * RH, 4, lu + 4 * q * RL), (hu + 4 * q * RH, 8, 4 * p * RL + 4 * RL)
    if kind == "cosLo":
        return (4 * p * RH, 6, lu + 4 * q * RL + 2 * RL), (hu + 4 * q * RH, 6, 4 * p * RL + 2 * RL)
    if kind == "sinHi":
        return (4 * p * RH, 7, lu + 4 * q * RL + 3 * RL), (hu + 4 * q * RH, 5, 4 * p * RL + RL)
    return (4 * p * RH, 5, lu + 4 * q * RL + RL), (hu + 4 * q * RH, 7, 4 * p * RL + 3 * RL)


def window(kind, lu, hu):
    """(p, q, B) for the side's no-extremum window — the exact inequalities of CosHi/CosLo/SinHi/SinLo — or None."""
    lu, hu = F(lu), F(hu)
    j0 = math.floor(float(lu) / (2 * math.pi))
    for j in range(j0 - 2, j0 + 3):
        p, q = (j, 0) if j >= 0 else (0, -j)
        (b1, k1, r1), (b2, k2, r2) = _ineq(kind, p, q, lu, hu)
        s1, s2 = r1 - b1, r2 - b2
        if s1 <= 0 or s2 <= 0:
            continue
        e = min(s1 / k1, s2 / k2)                    # the largest margin allowed
        B = max(1, (e.denominator // e.numerator).bit_length())     # 2^-B <= e
        while F(1, 2 ** B) > e:
            B += 1
        return p, q, B
    return None


def side_ok(which, lu, hu, lo, hi, side):
    """Lean witnesses for one side ('hi' or 'lo') of the kernel's [lo, hi] for which(x), x in [lu, hu]."""
    if side == "hi":
        if hi >= 1:
            return True
        return bool(pibr() and window(which + "Hi", lu, hu) and cert(lu, which, need_hi=hi) is not None
                    and cert(hu, which, need_hi=hi) is not None)
    if lo <= -1:
        return True
    return bool(pibr() and window(which + "Lo", lu, hu) and cert(lu, which, need_lo=lo) is not None
                and cert(hu, which, need_lo=lo) is not None)


def tan_end(q, T, low):
    """Certified sin, cos brackets at q: c_lo > 0 and T·c <= s_lo at both c ends (low) / s_hi <= T·c (high)."""
    q = F(q)
    a = abs(q)
    cr, ci, C, S, t = F(1), F(0), F(0), F(0), F(1)
    for m in range(MMAX + 1):
        if 2 * a <= m + 1:
            cl, ch, sl, sh = C - 2 * t, C + 2 * t, S - 2 * t, S + 2 * t
            if cl > 0 and ((low and T * cl <= sl and T * ch <= sl) or
                           (not low and sh <= T * cl and sh <= T * ch)):
                return m
        C += cr; S += ci
        cr, ci = (-ci) * q / (m + 1), cr * q / (m + 1)
        t = t * a / (m + 1)
    return None


def tan_ok(lu, hu, Tl, Th):
    """ZTrig.TanVal for the kernel's tan reading [Tl, Th] over [lu, hu] (ends rounded outward as the kernel does)."""
    lu, hu, Tl, Th = F(lu), F(hu), F(Tl), F(Th)
    q0, q1 = zfunc._down(lu), zfunc._up(hu)
    cmin = min(math.cos(float(q0)), math.cos(float(q1))) / 2
    if cmin <= 0:
        return False
    c0 = F(cmin)
    if not (pibr() and window("cosLo", q0, q1) and cert(q0, "cos", need_lo=c0) is not None
            and cert(q1, "cos", need_lo=c0) is not None):
        return False
    d = q1 - q0
    if not (window("sinLo", F(0), d) and cert(F(0), "sin", need_lo=F(0)) is not None
            and cert(d, "sin", need_lo=F(0)) is not None):
        return False
    return tan_end(q0, Tl, True) is not None and tan_end(q1, Th, False) is not None
