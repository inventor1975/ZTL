# -*- coding: utf-8 -*-
"""The certificate rule `ZExp.ExpCert` (lean/ZExp.lean), in exact fractions — the bridge between the kernel's
exp brackets and the Lean theorem `ZExp.bracket_sound` (a certified [lo, hi] contains exp x, on VR's operational
reals, zero axioms).

The kernel computes exp by argument reduction and squaring (zfunc.exp_pt); the Lean proof is about the plain
series. This module checks a bracket BY THE PROVED RULE: an index n with 2|x| <= n + 1, the partial sum
L = S_n(|x|) and H = L + 2 t_n(|x|); for x >= 0, lo <= L and H <= hi; for x < 0 (at index n + 1),
lo*H <= 1 <= hi*L. A bracket that passes is covered by the theorem, however the kernel computed it.
"""
import functools
from fractions import Fraction


def exp_cert(x, lo, hi, max_terms=5000):
    """(True, n) when [lo, hi] is certified for exp x by ZExp.ExpCert, else (False, reason).

    IN INTEGERS (2026-11-08, the curator's shakedown: the pump took 71 s on the server, 7.8 of 15 s here in this
    function's Fraction gcd): with |x| = n/d, every quantity at step k has the denominator Q_k = d^k·k!
    (t_k = n^k/Q_k, S_k carried as a numerator over Q_k); lo = p1/q1, hi = p2/q2 compared by cross-multiplying.
    The same decisions as `exp_cert_fr` (the Fractions reference, kept; test_expcert.py checks they agree)."""
    return _exp_cert_int(Fraction(x), Fraction(lo), Fraction(hi), max_terms)


@functools.lru_cache(maxsize=1 << 15)
def _exp_cert_int(x, lo, hi, max_terms):
    y = abs(x)
    n, d = y.numerator, y.denominator
    p1, q1, p2, q2 = lo.numerator, lo.denominator, hi.numerator, hi.denominator
    shift = 0 if x >= 0 else 1
    A, Sn, Q, k = 1, 0, 1, 0                      # t_k = A/Q, S_k = Sn/Q
    while k <= max_terms:
        good = 2 * n <= ((k - shift) + 1) * d and k >= shift
        if good:
            H = Sn + 2 * A                            # over Q
            if x >= 0 and p1 * Q <= Sn * q1 and H * q2 <= p2 * Q:
                return True, k
            if x < 0 and p1 * H <= q1 * Q and q2 * Q <= p2 * Sn:
                return True, k - 1
            if x >= 0 and (p1 * Q > H * q1 or p2 * Q < Sn * q2):
                break
            if x < 0 and (p1 * Sn > q1 * Q or p2 * H < q2 * Q):
                break
        Sn += A
        k += 1
        Sn *= d * k
        Q *= d * k
        A *= n
    return False, f"no index up to {max_terms} certifies [{float(lo)}, {float(hi)}] for exp({float(x)})"


def exp_cert_fr(x, lo, hi, max_terms=5000):
    """The reference: `exp_cert` in Fractions (the version before 2026-11-08)."""
    x, lo, hi = Fraction(x), Fraction(lo), Fraction(hi)
    y = abs(x)
    shift = 0 if x >= 0 else 1                    # x < 0: the rule reads index n + 1
    t, s, k = Fraction(1), Fraction(0), 0         # t = t_k, s = S_k
    while k <= max_terms:
        good = 2 * y <= (k - shift) + 1 and k >= shift
        if good:
            L, H = s, s + 2 * t
            if x >= 0 and lo <= L and H <= hi:
                return True, k
            if x < 0 and lo * H <= 1 <= hi * L:
                return True, k - 1
            # once good, L rises and H falls toward e^|x| (ZExp.S_between): past these points no later index
            # can certify, so stop (a bracket that misses e^x would otherwise run to max_terms)
            if x >= 0 and (lo > H or hi < L):
                break
            if x < 0 and (lo * L > 1 or hi * H < 1):
                break
        s += t
        k += 1
        t = t * y / k
    return False, f"no index up to {max_terms} certifies [{float(lo)}, {float(hi)}] for exp({float(x)})"
