# -*- coding: utf-8 -*-
"""
FUNCTIONS ON THE NUMERIC FLOOR — exp, ln, log10, atan, tan, pow, min, max.

WHY (2026-10-10, the universal stand's blind test): eleven problems of twelve needed a
function the floor did not have, so the authors bounded it by hand, OUTSIDE the judge.

HOW, AND WHY IT STAYS EXACT. The floor computes in fractions, and these functions are
irrational almost everywhere. So each value is a PROVED BRACKET of two rationals — the
same honesty as `_rat_sqrt`: not a rounding, a fork that says what it does not know. Every
series below has a remainder bound, and every bracket is rounded OUTWARD onto a grid of
2^-BITS, so the true value is always inside. Over an interval, a monotone function maps the
ends (exp, ln, log10, atan, tan on (-pi/2, pi/2)); pow is exp(y·ln x) for x > 0 (an integer
exponent is an exact interval power); min and max are exact.

Domain, the floor's three outcomes as for sqrt: an interval wholly outside the domain has
NO readings (`NoReadings`); one that touches the edge gives None (some readings undefined:
a mark, not a verdict); one inside gives the bracket.

No budget in the sense of the decision of 2026-10-09: the precision is fixed (BITS), the
work is a fixed number of series terms for it, and the answer is always a sound bracket.
"""

from fractions import Fraction
import math

BITS = 64                      # bracket grid 2^-64 relative-ish; every series sized for it
_EPS = Fraction(1, 1 << (BITS + 8))


class NoReadings(Exception):
    pass


# ---------------------------------------------------------------- rounding outward
def _down(x: Fraction, bits=BITS) -> Fraction:
    """The largest dyadic m/2^k <= x, k chosen from x's size (keeps fractions small)."""
    if x == 0:
        return Fraction(0)
    # a RELATIVE grid: the exponent follows x's own size, small numbers too (a fixed 2^-64 grid
    # rounded e^-100 to [0, 5e-20] — sound, and useless; caught by the width check 2026-10-10)
    e = max(0, bits - (abs(x).numerator.bit_length() - abs(x).denominator.bit_length()))
    s = 1 << e
    return Fraction(math.floor(x * s), s)


def _up(x: Fraction, bits=BITS) -> Fraction:
    return -_down(-x, bits)


# ---------------------------------------------------------------- constants
def _atan_small(x: Fraction, terms: int):
    """atan(x) for |x| <= 1/2 by its alternating series; the remainder is below the next term."""
    s, p, sign = Fraction(0), x, 1
    x2 = x * x
    for i in range(terms):
        s += sign * p / (2 * i + 1)
        p *= x2
        sign = -sign
    rem = abs(p) / (2 * terms + 1)
    return s - rem, s + rem


def _pi():
    """Machin: pi = 16 atan(1/5) - 4 atan(1/239)."""
    a = _atan_small(Fraction(1, 5), 40)
    b = _atan_small(Fraction(1, 239), 12)
    return 16 * a[0] - 4 * b[1], 16 * a[1] - 4 * b[0]


def _atanh_series(z: Fraction, terms: int):
    """atanh(z) = sum z^(2i+1)/(2i+1) for |z| < 1; the tail <= |z|^(2N+1) / ((2N+1)(1 - z^2))."""
    s, p = Fraction(0), z
    z2 = z * z
    for i in range(terms):
        s += p / (2 * i + 1)
        p *= z2
    rem = abs(p) / ((2 * terms + 1) * (1 - z2))
    return s - rem, s + rem


def _ceil_div(a: int, b: int) -> int:
    return -((-a) // b)


def _atanh_fixed(z: Fraction, terms: int, P: int):
    """atanh(z), |z| <= 1/4, in FIXED POINT: integers scaled by 2^P, every step rounded DOWN for the lower
    sum and UP for the upper one (all terms positive for z >= 0; atanh is odd). Sound like _atanh_series,
    with no growing fractions (MEASURED 2026-10-10: ln of a diode law, 1.7 ms -> microseconds a call)."""
    neg = z < 0
    z = -z if neg else z
    S = 1 << P
    zl, zh = (z.numerator * S) // z.denominator, _ceil_div(z.numerator * S, z.denominator)
    z2l, z2h = (zl * zl) >> P, _ceil_div(zh * zh, S)
    pl, ph, sl, sh = zl, zh, 0, 0
    for i in range(terms):
        sl += pl // (2 * i + 1)
        sh += _ceil_div(ph, 2 * i + 1)
        pl = (pl * z2l) >> P
        ph = _ceil_div(ph * z2h, S)
    rem = Fraction(ph, S) / ((2 * terms + 1) * (1 - Fraction(z2h, S)))   # the tail, bounded from above
    lo, hi = Fraction(sl, S), Fraction(sh, S) + rem
    return (-hi, -lo) if neg else (lo, hi)


def _exp_fixed(a: Fraction, P: int, stop: Fraction):
    """e^a for 0 <= a <= 1/4 in fixed point, rounded outward each step; the tail after a term t with
    a <= 1/4 is below t, so hi adds 2t as the old code did."""
    S = 1 << P
    al, ah = (a.numerator * S) // a.denominator, _ceil_div(a.numerator * S, a.denominator)
    tl, th, sl, sh, n = S, S, S, S, 0
    stop_fixed = stop * S
    while True:
        n += 1
        tl = ((tl * al) >> P) // n
        th = _ceil_div(_ceil_div(th * ah, S), n)
        sl += tl
        sh += th
        if th < stop_fixed and n > 4:
            break
    return Fraction(sl, S), Fraction(sh + 2 * th, S)


def _ln2():
    lo, hi = _atanh_series(Fraction(1, 3), 45)      # ln 2 = 2 atanh(1/3)
    return 2 * lo, 2 * hi


PI = tuple(_down(v) if i == 0 else _up(v) for i, v in enumerate(_pi()))
LN2 = tuple(_down(v) if i == 0 else _up(v) for i, v in enumerate(_ln2()))


# ---------------------------------------------------------------- points
def exp_pt(x: Fraction):
    """[lo, hi] around e^x. Reduce: x = t·2^m with |t| <= 1/4, Taylor on t, then square m times."""
    x = Fraction(x)
    if abs(x) > 50_000:
        raise NoReadings("exp of an argument past 50000: outside any physical range")
    m = 0
    t = x
    while abs(t) > Fraction(1, 4):
        t /= 2
        m += 1
    # fixed point on |t| (MEASURED 2026-10-10: exact-fraction Taylor was 0.6 ms a call); e^-a = 1/e^a
    P = BITS + 40 + m
    elo, ehi = _exp_fixed(abs(t), P, _EPS / (1 << m) / 4)
    if t < 0:
        elo, ehi = 1 / ehi, 1 / elo
    lo, hi = _down(elo), _up(ehi)
    for _ in range(m):
        lo, hi = _down(lo * lo), _up(hi * hi)
    return lo, hi


def ln_pt(x: Fraction):
    """[lo, hi] around ln x, x > 0. x = 2^e·y with y in [1/2, 1]... [2/3, 4/3]; ln y = 2 atanh((y-1)/(y+1))."""
    x = Fraction(x)
    if x <= 0:
        raise NoReadings("ln of a value that is not positive")
    if x == 1:
        return Fraction(0), Fraction(0)
    e = x.numerator.bit_length() - x.denominator.bit_length()
    y = x / Fraction(2) ** e
    while y > Fraction(4, 3):
        y /= 2
        e += 1
    while y < Fraction(2, 3):
        y *= 2
        e -= 1
    z = (y - 1) / (y + 1)                      # |z| <= 1/5
    a = _atanh_fixed(z, 30, BITS + 40)
    lo = 2 * a[0] + (e * LN2[0] if e >= 0 else e * LN2[1])
    hi = 2 * a[1] + (e * LN2[1] if e >= 0 else e * LN2[0])
    return _down(lo), _up(hi)


def atan_pt(x: Fraction):
    """[lo, hi] around atan x. |x| > 1: pi/2 - atan(1/x). Then halve the argument twice:
    atan x = 2 atan(x / (1 + sqrt(1 + x^2))) — the root is itself bracketed."""
    x = Fraction(x)
    if x == 0:
        return Fraction(0), Fraction(0)
    if x < 0:
        lo, hi = atan_pt(-x)
        return -hi, -lo
    if x > 1:
        lo, hi = atan_pt(1 / x)
        return _down(PI[0] / 2 - hi), _up(PI[1] / 2 - lo)
    if x <= Fraction(1, 2):
        lo, hi = _atan_small(x, 70)
        return _down(lo), _up(hi)
    # 1/2 < x <= 1: atan x = atan(1/2) + atan((x - 1/2)/(1 + x/2))
    y = (x - Fraction(1, 2)) / (1 + x / 2)    # 0 < y <= 2/5
    a, b = _atan_small(Fraction(1, 2), 70), _atan_small(y, 70)
    return _down(a[0] + b[0]), _up(a[1] + b[1])


def sincos_pt(x: Fraction):
    """([sin lo, hi], [cos lo, hi]) for |x| <= 2 by Taylor; the remainder is below the next term."""
    x = Fraction(x)
    if abs(x) > 2:
        raise NoReadings("sin/cos outside |x| <= 2 not supported here")
    s, c = Fraction(0), Fraction(0)
    term_s, term_c = x, Fraction(1)
    for n in range(40):
        s += term_s
        c += term_c
        term_s = -term_s * x * x / ((2 * n + 2) * (2 * n + 3))
        term_c = -term_c * x * x / ((2 * n + 1) * (2 * n + 2))
    rs, rc = abs(term_s), abs(term_c)
    return (_down(s - rs), _up(s + rs)), (_down(c - rc), _up(c + rc))


def tan_pt(x: Fraction):
    (slo, shi), (clo, chi) = sincos_pt(x)
    if clo <= 0:
        raise NoReadings("tan near or past pi/2")
    cands = [a / b for a in (slo, shi) for b in (clo, chi)]
    return _down(min(cands)), _up(max(cands))


# ---------------------------------------------------------------- intervals
INF = float("inf")


def _inf(x):
    return isinstance(x, float) and x in (INF, -INF)


def _iv_mono(f, a, at_minus_inf=None, at_plus_inf=None):
    """An increasing function over [a0, a1]; an INFINITE end (the floor's unbounded boxes are
    float +-inf) maps to the function's limit there, given by the caller."""
    # each end ROUNDED OUTWARD onto the 2^-BITS relative grid before the series: f increasing, so
    # f(down(a0)) <= f(a0) and f(up(a1)) >= f(a1) — sound, ~2^-64 wider. The series then runs on a
    # 64-bit dyadic, not on the reading's exact fraction with a denominator of hundreds of digits
    # (MEASURED 2026-10-10, blind test 2 c04 — a diode law: 92 % of the run in ln's atanh series)
    lo = at_minus_inf if (_inf(a[0]) and a[0] < 0) else (at_plus_inf if _inf(a[0]) else f(_down(Fraction(a[0])))[0])
    hi = at_plus_inf if (_inf(a[1]) and a[1] > 0) else (at_minus_inf if _inf(a[1]) else f(_up(Fraction(a[1])))[1])
    return lo, hi


def iv_exp(a):
    return _iv_mono(exp_pt, a, Fraction(0), INF)


def iv_ln(a):
    if a[1] <= 0:
        raise NoReadings("ln of a quantity that is never positive")
    if a[0] <= 0:
        return None
    return _iv_mono(ln_pt, a, -INF, INF)


LN10 = ln_pt(Fraction(10))


def iv_log10(a):
    r = iv_ln(a)
    if r is None:
        return None
    lo, hi = r
    l2 = -INF if _inf(lo) else _down(min(lo / LN10[0], lo / LN10[1]))
    h2 = INF if _inf(hi) else _up(max(hi / LN10[0], hi / LN10[1]))
    return l2, h2


def iv_atan(a):
    return _iv_mono(atan_pt, a, -PI[1] / 2, PI[1] / 2)


TAN_EDGE = Fraction(3, 2)        # below pi/2 = 1.5707...: tan is read only on |x| <= 1.5


def iv_tan(a):
    if _inf(a[0]) or _inf(a[1]):
        return None
    if a[0] > TAN_EDGE or a[1] < -TAN_EDGE:
        raise NoReadings("tan read only on |x| <= 1.5 (below pi/2)")
    if a[0] < -TAN_EDGE or a[1] > TAN_EDGE:
        return None
    return _iv_mono(tan_pt, a)


def _ipow_point(x: Fraction, n: int):
    return x ** n


def iv_pow(a, b):
    """a^b. An integer exponent (b a point integer): the exact interval power. Otherwise a > 0:
    exp(b·ln a), sound (decorrelated, so it may be wider than the truth)."""
    if any(_inf(x) for x in (*a, *b)):
        return None                       # an unbounded base or exponent: a mark, not a value
    if b[0] == b[1] and Fraction(b[0]).denominator == 1:
        n = int(b[0])
        if n == 0:
            return Fraction(1), Fraction(1)
        if n < 0:
            if a[0] <= 0 <= a[1]:
                return None
            p = iv_pow(a, (Fraction(-n), Fraction(-n)))
            cands = [1 / p[0], 1 / p[1]]
            return min(cands), max(cands)
        ends = [a[0] ** n, a[1] ** n]
        if n % 2 == 0 and a[0] < 0 < a[1]:
            return Fraction(0), max(ends)
        return min(ends), max(ends)
    if a[1] <= 0:
        raise NoReadings("a non-integer power of a quantity that is never positive")
    if a[0] <= 0:
        return None
    l = iv_ln(a)
    cands = [x * y for x in l for y in b]
    return iv_exp((min(cands), max(cands)))


def iv_min(a, b):
    return min(a[0], b[0]), min(a[1], b[1])


def iv_max(a, b):
    return max(a[0], b[0]), max(a[1], b[1])


UNARY = {"exp": iv_exp, "ln": iv_ln, "log10": iv_log10, "atan": iv_atan, "tan": iv_tan}
BINARY = {"pow": iv_pow, "min": iv_min, "max": iv_max}
FUNC_OPS = set(UNARY) | set(BINARY)
