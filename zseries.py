# -*- coding: utf-8 -*-
"""
FUNCTIONS GIVEN BY A POWER SERIES on the numeric floor — Bessel J0, J1 and Kelvin ber, bei, and every derivative of
them (2026-11-09, the curator: «Добавь в ядро Бессель и интегралы»; ztl-stand physics round 1: the skin effect of
a steel rod and a two-hole interferometer needed Bessel functions the floor did not have, and were computed in
Python OUTSIDE the judge).

A family f(x) = sum_k c_k x^(e_k), e_k = e_0 + s·k (s the step), c_k rational and ALTERNATING in sign, |c_k| from a
closed form. The names:
    besselj0   J0(x)  = sum (-1)^k (x/2)^(2k) / (k!)^2
    besselj1   J1(x)  = sum (-1)^k (x/2)^(2k+1) / (k! (k+1)!)
    ber        ber(x) = sum (-1)^k (x/2)^(4k) / ((2k)!)^2
    bei        bei(x) = sum (-1)^k (x/2)^(4k+2) / ((2k+1)!)^2
    <name>_d<n>        the n-th derivative, term by term (the same alternation; e_k − n, c_k · e_k (e_k−1)…)
    berp, beip         ber', bei' (aliases of ber_d1, bei_d1) — the skin-effect formula's own words.

A POINT x (rational): the terms t_k = c_k x^(e_k). Their signs alternate for every k (x^(e_k) has one sign for all k:
e_k all even, or all odd with one sign of x). Once |t_k| decreases for good — the ratio |t_(k+1)/t_k| =
|x|^s |c_(k+1)/c_k| is DECREASING in k (each family's c-ratio is a product of 1/(k+j) factors) and below 1 — the sum
lies between two consecutive partial sums (the alternating-series bound). The bracket is those two sums, rounded
outward onto the floor's 2^-BITS grid.

AN INTERVAL [a0, a1]: a dyadic point m inside, radius r = max(m − a0, a1 − m), the second-derivative bound
D2 = sum_k |c_k| e_k (e_k − 1) R^(e_k − 2), R = max |a| (a series of positive terms, increasing in R — its tail, once the
ratio is below 1/2 and decreasing, is at most the last term); then f([a]) ⊂ f(m) ± |f'(m)|·r + D2·r²/2 (Taylor). Sharper where the derivative's
own reading keeps one sign: f is monotone there and the ends' brackets bound it. J0 and J1 are also clamped to [−1, 1]
(|J_n(x)| ≤ 1 for real x).

SAID, NOT HIDDEN: the alternating-series bound and the ratio's monotonicity are the premises (classical, checked here
numerically for every k used); there are no Lean witnesses for these functions yet (exp, ln, sin, cos, atan have them).
"""
from fractions import Fraction
import math

class _LazyZF:
    """zfunc, read at call time: zfunc imports this module to register the names (a cycle at import time)."""
    def __getattr__(self, k):
        import zfunc
        return getattr(zfunc, k)


ZF = _LazyZF()

FAMILIES = {
    # name: (e0, step, |c_k| as a function of k)
    "besselj0": (0, 2, lambda k: Fraction(1, 4 ** k * math.factorial(k) ** 2)),
    "besselj1": (1, 2, lambda k: Fraction(1, 2 ** (2 * k + 1) * math.factorial(k) * math.factorial(k + 1))),
    "ber": (0, 4, lambda k: Fraction(1, 2 ** (4 * k) * math.factorial(2 * k) ** 2)),
    "bei": (2, 4, lambda k: Fraction(1, 2 ** (4 * k + 2) * math.factorial(2 * k + 1) ** 2)),
}
BOUNDED = {"besselj0", "besselj1"}            # |J_n| <= 1 on the reals
ALIASES = {"berp": "ber_d1", "beip": "bei_d1"}
MAX_TERMS = 4000


def split(name):
    """('ber', 2) for 'ber_d2'; (name, 0) for a base; aliases resolved; None when not a series function."""
    name = ALIASES.get(name, name)
    base, _, d = name.partition("_d")
    if base not in FAMILIES or (d and not d.isdigit()):
        return None
    return base, int(d) if d else 0


def is_series(name):
    return split(name) is not None


def derivative_name(name):
    base, n = split(name)
    return f"{base}_d{n + 1}"


def _terms(base, n):
    """Yields (k, sign, |coefficient|, exponent) of the n-th derivative, k from the first non-vanishing term."""
    e0, s, c = FAMILIES[base]
    k = 0
    while True:
        e = e0 + s * k
        if e >= n:
            coef = c(k)
            for j in range(n):
                coef *= (e - j)
            yield k, (-1) ** k, coef, e - n
        k += 1
        if k > MAX_TERMS:
            raise ArithmeticError("series: too many terms")


def point(name, x):
    """A proved bracket of f(x) at a rational x."""
    base, n = split(name)
    x = Fraction(x)
    if x == 0:
        for k, sg, coef, e in _terms(base, n):
            return (sg * coef, sg * coef) if e == 0 else (Fraction(0), Fraction(0))
    s_prev, prev_abs, prev_ratio = Fraction(0), None, None
    partial = Fraction(0)
    for k, sg, coef, e in _terms(base, n):
        t = sg * coef * x ** e
        partial += t
        a = abs(t)
        if prev_abs is not None and prev_abs > 0:
            ratio = a / prev_abs
            # decreasing for good: the ratio below 1, and below the previous ratio (decreasing in k, the premise)
            if ratio < 1 and (prev_ratio is None or ratio <= prev_ratio) and a < Fraction(1, 1 << (ZF.BITS + 16)) * (1 + abs(partial)):
                # true value between the partial sums before and after this term (alternating, decreasing)
                lo, hi = min(s_prev, partial), max(s_prev, partial)
                return ZF._down(lo), ZF._up(hi)
            prev_ratio = ratio
        s_prev, prev_abs = partial, a
    raise ArithmeticError("series: no convergence")


def _abs_series_bound(base, n, R):
    """An upper bound of sum_k |c_k| e_k R^(e_k − 1) for the n-th derivative's own derivative, R >= 0 rational: the
    bound of |f^(n+1)| on [−R, R]. Positive terms; the tail after a term t with ratio q <= 1/2, q decreasing, is <= t."""
    R = Fraction(R)
    total, prev, prev_q = Fraction(0), None, None
    for k, sg, coef, e in _terms(base, n + 1):
        t = coef * R ** e
        total += t
        if prev is not None and prev > 0:
            q = t / prev
            if q <= Fraction(1, 2) and (prev_q is None or q <= prev_q) and t < Fraction(1, 1 << (ZF.BITS + 16)) * (1 + total):
                return total + t                   # the tail <= t (geometric, ratio <= 1/2)
            prev_q = q
        prev = t
        if R == 0 and k > 1:
            return total
    raise ArithmeticError("series bound: no convergence")


def _mid(a0, a1):
    m = (a0 + a1) / 2
    return ZF._down(m) if a0 <= ZF._down(m) <= a1 else m


def _taylor2(name, a0, a1):
    """f(x) = f(m) + f'(m)(x − m) + f''(xi)(x − m)²/2: f([a]) ⊂ f(m) ± |f'(m)|·r + D2·r²/2, D2 a bound of |f''| on
    [−R, R] (the positive series). MEASURED 2026-11-09: the first-order form (f(m) ± D1·r) was 22× wider than the
    true spread in the median of 225 random intervals; this one hugs it as r shrinks."""
    base, n = split(name)
    m = _mid(a0, a1)
    r = max(m - a0, a1 - m)
    R = max(abs(a0), abs(a1))
    D2 = _abs_series_bound(base, n + 1, R)
    lo, hi = point(name, m)
    dlo, dhi = point(derivative_name(name), m)
    slope = max(abs(dlo), abs(dhi))
    return ZF._down(lo - slope * r - D2 * r * r / 2), ZF._up(hi + slope * r + D2 * r * r / 2)


def interval(name, a):
    """A proved enclosure of f over [a0, a1]."""
    base, n = split(name)
    if ZF._inf(a[0]) or ZF._inf(a[1]):
        if base in BOUNDED and n == 0:
            return Fraction(-1), Fraction(1)
        return None
    a0, a1 = Fraction(a[0]), Fraction(a[1])
    if a0 == a1:
        out = point(name, a0)
    else:
        out = _taylor2(name, a0, a1)
        d = _taylor2(derivative_name(name), a0, a1)            # the derivative's reading over the interval
        if d[0] > 0 or d[1] < 0:                               # one sign: monotone — the ends bound it
            p0, p1 = point(name, a0), point(name, a1)
            mono = (min(p0[0], p1[0]), max(p0[1], p1[1]))
            out = (max(out[0], mono[0]), min(out[1], mono[1]))
    if base in BOUNDED and n == 0:
        out = (max(out[0], Fraction(-1)), min(out[1], Fraction(1)))
    return out


def unary(name):
    """The floor's reader for one name: interval -> enclosure."""
    return lambda a: interval(name, a)
