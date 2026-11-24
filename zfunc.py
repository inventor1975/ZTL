# -*- coding: utf-8 -*-
"""
FUNCTIONS ON THE NUMERIC FLOOR — exp, ln, log10, atan, tan, sin, cos, pow, min, max.

WHY (2026-10-10, the universal stand's blind test): eleven problems of twelve needed a
function the floor did not have, so the authors bounded it by hand, OUTSIDE the judge.

HOW, AND WHY IT STAYS EXACT. The floor computes in fractions, and these functions are
irrational almost everywhere. So each value is a PROVED BRACKET of two rationals — the
same honesty as `_rat_sqrt`: not a rounding, a fork that says what it does not know. Every
series below has a remainder bound, and every bracket is rounded OUTWARD onto a grid of
2^-BITS, so the true value is always inside. Over an interval, a monotone function maps the
ends (exp, ln, log10, atan, tan on (-pi/2, pi/2)); sin and cos (2026-10-13, the universal stand's blind test 6,
the curator's "да") map the ends and take +-1 wherever an extremum may lie inside, the argument reduced through
pi's own bracket; pow is exp(y·ln x) for x > 0 (an integer exponent is an exact interval power); min and max are
exact.

Domain, the floor's three outcomes as for sqrt: an interval wholly outside the domain has
NO readings (`NoReadings`); one that touches the edge gives None (some readings undefined:
a mark, not a verdict); one inside gives the bracket.

No budget in the sense of the decision of 2026-10-09: the precision is fixed (BITS), the
work is a fixed number of series terms for it, and the answer is always a sound bracket.
"""

from fractions import Fraction
from zgap import gap, is_gap
import functools
import math

BITS = 64                      # bracket grid 2^-64 relative-ish; every series sized for it
_EPS = Fraction(1, 1 << (BITS + 8))


class NoReadings(Exception):
    pass


class FloorLimit(NoReadings):
    """THE FLOOR CANNOT READ IT — not "there is nothing to read" (2026-11-24, the curator's "1+2 делаем"). Until then
    every limit of these series (exp past 50000, tan past 1.5, a failed sin/cos reduction) was raised as NoReadings and
    the judge answered E, "no subject, repair the claim", for tan(46) and exp(60000), which exist (MEASURED: tan(46) >
    -100 -> E). A SUBCLASS on purpose: the certificate checkers that stop on NoReadings stop on this too (they cannot
    read it either); only the judge (znum) tells the two apart — a limit is a mark with its reason, never E."""


# ---------------------------------------------------------------- rounding outward
def _down(x: Fraction, bits=BITS) -> Fraction:
    """The largest dyadic m/2^k <= x, k chosen from x's size (keeps fractions small)."""
    if x == 0:
        return Fraction(0)
    # a RELATIVE grid: the exponent follows x's own size, small numbers too (a fixed 2^-64 grid
    # rounded e^-100 to [0, 5e-20] — sound, and useless; caught by the width check 2026-10-10)
    e = max(0, bits - (abs(x).numerator.bit_length() - abs(x).denominator.bit_length()))
    s = 1 << e
    # floor(x·2^e) in integers: Python's // floors for negatives too — the same number as math.floor(x * s), without
    # the Fraction product's gcd (2026-11-08, the pump's shakedown: 1.9 s of 8 here)
    x = Fraction(x)
    return Fraction((x.numerator * s) // x.denominator, s)


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


def _atan_fixed(x: Fraction, terms: int, P: int):
    """atan(x), 0 <= x <= 1/2, in FIXED POINT (2^P), like _atanh_fixed: each term x^(2i+1)/(2i+1) bracketed
    [tl, th] by rounding down / up, the alternating sum taken at its lower and upper ends, and the tail after
    `terms` terms bounded by the next term's upper bracket on both sides. MEASURED 2026-10-11 (blind test 5,
    c04, the sewer's circular segment): the exact-fraction series took 137 of 150 s, 86 s of it in gcd."""
    S = 1 << P
    xl, xh = (x.numerator * S) // x.denominator, _ceil_div(x.numerator * S, x.denominator)
    x2l, x2h = (xl * xl) >> P, _ceil_div(xh * xh, S)
    pl, ph, lo, hi = xl, xh, 0, 0
    for i in range(terms):
        tl, th = pl // (2 * i + 1), _ceil_div(ph, 2 * i + 1)
        if i % 2 == 0:
            lo, hi = lo + tl, hi + th
        else:
            lo, hi = lo - th, hi - tl
        pl = (pl * x2l) >> P
        ph = _ceil_div(ph * x2h, S)
    tail = _ceil_div(ph, 2 * terms + 1)
    return Fraction(lo - tail, S), Fraction(hi + tail, S)


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
ATAN_HALF = tuple(_down(v) if i == 0 else _up(v) for i, v in enumerate(_atan_small(Fraction(1, 2), 70)))   # once, exact series


# ---------------------------------------------------------------- points
def exp_pt(x: Fraction):
    """[lo, hi] around e^x. Reduce: x = t·2^m with |t| <= 1/4, Taylor on t, then square m times."""
    x = Fraction(x)
    if abs(x) > 50_000:
        raise FloorLimit("exp of an argument past 50000 is not read by the floor")
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
        lo, hi = _atan_fixed(x, 60, BITS + 40)
        return _down(lo), _up(hi)
    # 1/2 < x <= 1: atan x = atan(1/2) + atan((x - 1/2)/(1 + x/2))
    y = (x - Fraction(1, 2)) / (1 + x / 2)    # 0 < y <= 2/5
    a, b = ATAN_HALF, _atan_fixed(y, 60, BITS + 40)
    return _down(a[0] + b[0]), _up(a[1] + b[1])


def sincos_pt(x: Fraction):
    """([sin lo, hi], [cos lo, hi]) for |x| <= 2 by Taylor; the remainder is below the next term."""
    x = Fraction(x)
    if abs(x) > 2:
        raise FloorLimit("sin/cos outside |x| <= 2 not supported here")
    return _sc_series(x)


_F80 = [1] * 81                       # 80!/j!
for _j in range(80, 0, -1):
    _F80[_j - 1] = _F80[_j] * _j
_FACT81 = math.factorial(81)


@functools.lru_cache(maxsize=1 << 15)
def _sc_series(x: Fraction):
    """The Taylor sums for |x| <= 4 (40 terms: the next term below 4^81/81! ~ 1e-72); alternating with terms
    falling from the first one past |x|, so the remainder is below the next term's size.

    IN INTEGERS (2026-11-08, the curator: "если знаешь как улучшить — делай"): with x = n/d, x^j/j! =
    n^j·d^(80−j)·(80!/j!) / (d^80·80!) — the forty terms summed as integers over one denominator, then ONE
    Fraction. The same exact sums as `_sc_series_fr` (the reference, test_trigcert.py checks they agree), with no
    gcd per term. MEASURED: Fraction's gcd was ~60% of a ZFL system with cos (cProfile, 9.7 s of 11.8)."""
    x = Fraction(x)
    if abs(x) > 4:
        raise FloorLimit("sin/cos series only for |x| <= 4")
    n, d = x.numerator, x.denominator
    npow = [1] * 82
    for j in range(1, 82):
        npow[j] = npow[j - 1] * n
    dpow = [1] * 82
    for j in range(1, 82):
        dpow[j] = dpow[j - 1] * d
    sn = cn = 0
    for k in range(40):
        sg = -1 if k % 2 else 1
        cn += sg * npow[2 * k] * dpow[80 - 2 * k] * _F80[2 * k]
        sn += sg * npow[2 * k + 1] * dpow[79 - 2 * k] * _F80[2 * k + 1]
    D = dpow[80] * _F80[0]
    s, c = Fraction(sn, D), Fraction(cn, D)
    rs = Fraction(abs(npow[81]), dpow[81] * _FACT81)
    rc = Fraction(abs(npow[80]), D)
    return (_down(s - rs), _up(s + rs)), (_down(c - rc), _up(c + rc))


def _sc_series_fr(x: Fraction):
    """The reference: `_sc_series` in Fractions (the version before 2026-11-08)."""
    x = Fraction(x)
    if abs(x) > 4:
        raise FloorLimit("sin/cos series only for |x| <= 4")
    s, c = Fraction(0), Fraction(0)
    term_s, term_c = x, Fraction(1)
    for n in range(40):
        s += term_s
        c += term_c
        term_s = -term_s * x * x / ((2 * n + 2) * (2 * n + 3))
        term_c = -term_c * x * x / ((2 * n + 1) * (2 * n + 2))
    rs, rc = abs(term_s), abs(term_c)
    return (_down(s - rs), _up(s + rs)), (_down(c - rc), _up(c + rc))


TWO_PI = (2 * PI[0], 2 * PI[1])


def _reduced(x: Fraction):
    """x - 2 pi k as an INTERVAL [r1, r2] (pi is itself a bracket), k = round(x / 2pi): |r| <= ~pi."""
    x = Fraction(x)
    k = round(float(x) / (2 * math.pi))
    if k == 0:
        return x, x
    a, b = x - k * TWO_PI[0], x - k * TWO_PI[1]
    return min(a, b), max(a, b)


def _sc_pt(x: Fraction, which: int):
    """[lo, hi] around sin x (which 0) or cos x (which 1), any x: reduced into |r| <= ~pi; sin and cos are
    1-Lipschitz, so the reduction's own width (from pi's bracket) widens the bracket by exactly that width."""
    r1, r2 = _reduced(x)
    if abs(r1) > 4 or abs(r2) > 4:
        raise FloorLimit("sin/cos: argument reduction failed")
    w = r2 - r1
    lo, hi = _sc_series(r1)[which]
    return _down(max(Fraction(-1), lo - w)), _up(min(Fraction(1), hi + w))


def sin_pt(x: Fraction):
    return _sc_pt(x, 0)


def cos_pt(x: Fraction):
    return _sc_pt(x, 1)


def tan_pt(x: Fraction):
    (slo, shi), (clo, chi) = sincos_pt(x)
    if clo <= 0:
        raise FloorLimit("tan near pi/2 is not read by the floor")
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


# EVERY ln reading is checked for the Lean witnesses of ZSlopeSqrt.VRead.ln (2026-10-17): its low side L needs an
# ExpCert of e^L whose top is <= the argument's low end, its high side one whose bottom is >= the argument's high end
# (zexpcert, lean/ZExp ExpCert). MEASURED: ln_pt's brackets are tighter than exp_pt's, 5955 of 6000 sides had no
# certificate as computed; moved outward by 2^-55 all 4000 of a second sample had one. A side is moved by the first
# margin that certifies; one that none does is kept and counted (LN_UNCOVERED) — a premise.
LN_UNCOVERED = [0]
_LN_MARGINS = (Fraction(0), Fraction(1, 2 ** 55), Fraction(1, 2 ** 30), Fraction(1, 2 ** 10))
_LN_CERT = {}


def _ln_side(u, L, side):
    key = (u, L, side)
    if key not in _LN_CERT:
        from zexpcert import exp_cert
        lo, hi = exp_pt(L)
        ok = exp_cert(L, lo, hi)[0] and (hi <= u if side == "lo" else lo >= u)
        _LN_CERT[key] = ok
    return _LN_CERT[key]


def _cert_ln(a, r):
    lo, hi = r
    if not (_inf(lo) or _inf(a[0])):
        u = Fraction(a[0])
        for m in _LN_MARGINS:
            if _ln_side(u, Fraction(lo) - m, "lo"):
                lo = Fraction(lo) - m
                break
        else:
            LN_UNCOVERED[0] += 1
    if not (_inf(hi) or _inf(a[1])):
        u = Fraction(a[1])
        for m in _LN_MARGINS:
            if _ln_side(u, Fraction(hi) + m, "hi"):
                hi = Fraction(hi) + m
                break
        else:
            LN_UNCOVERED[0] += 1
    return lo, hi


def iv_ln(a):
    if a[1] <= 0:
        raise NoReadings("ln of a quantity that is never positive")
    if a[0] <= 0:
        # AN EXCLUDED 0 (zgap.py, 2026-11-24): every reading is positive, ln runs down to -inf. A closed or negative
        # low end keeps the old answer: some readings undefined, a mark.
        if a[0] == 0 and is_gap(a[0]):
            a = (-INF, a[1])
            return _cert_ln(a, _iv_mono(ln_pt, a, -INF, INF))
        return None
    return _cert_ln(a, _iv_mono(ln_pt, a, -INF, INF))


LN10 = _cert_ln((Fraction(10), Fraction(10)), ln_pt(Fraction(10)))


def ln_pt_cert(x):
    """ln_pt with its sides certified as iv_ln's (zaffine's min-range reads ln at the ends of an interval)."""
    x = Fraction(x)
    return _cert_ln((x, x), ln_pt(x))


def iv_log10(a):
    r = iv_ln(a)
    if r is None:
        return None
    lo, hi = r
    l2 = -INF if _inf(lo) else _down(min(lo / LN10[0], lo / LN10[1]))
    h2 = INF if _inf(hi) else _up(max(hi / LN10[0], hi / LN10[1]))
    return l2, h2


# Lean's atan (lean/ZAtan.lean) is the grid sum of 1/(1 + t²); VRead.atan takes atan at the ends of the argument's
# reading as two facts about rational points, certified by a Taylor chain from atan 0 = 0 (lean/ZAtanCert.lean,
# zatancert). As for ln: each side moved outward by the first margin the chain certifies; none -> kept, counted.
ATAN_UNCOVERED = [0]
_ATAN_MARGINS = (Fraction(0), Fraction(1, 2 ** 55), Fraction(1, 2 ** 30), Fraction(1, 2 ** 10))


def _cert_atan(a, r):
    from zatancert import atan_cert
    lo, hi = r
    if not (_inf(lo) or _inf(a[0])):
        L = atan_cert(Fraction(a[0]))[0]
        for m in _ATAN_MARGINS:
            if L >= Fraction(lo) - m:
                lo = Fraction(lo) - m
                break
        else:
            ATAN_UNCOVERED[0] += 1
    if not (_inf(hi) or _inf(a[1])):
        H = atan_cert(Fraction(a[1]))[1]
        for m in _ATAN_MARGINS:
            if H <= Fraction(hi) + m:
                hi = Fraction(hi) + m
                break
        else:
            ATAN_UNCOVERED[0] += 1
    return lo, hi


def iv_atan(a):
    return _cert_atan(a, _iv_mono(atan_pt, a, -PI[1] / 2, PI[1] / 2))


def atan_pt_cert(x):
    """atan_pt with its sides certified as iv_atan's (zaffine's min-range reads atan at the ends)."""
    x = Fraction(x)
    return _cert_atan((x, x), atan_pt(x))


TAN_EDGE = Fraction(3, 2)        # below pi/2 = 1.5707...: tan is read only on |x| <= 1.5


def iv_tan(a):
    if _inf(a[0]) or _inf(a[1]):
        return None
    # TAN'S PERIOD (2026-11-24, with FloorLimit): tan(x) = tan(x - k pi), k = round(mid / pi), the shift taken with pi's
    # own bracket (the reduced interval is wider by k times its width). Until then tan was read on |x| <= 1.5 only and
    # tan(46) was E. The period is a Python reading; the Lean witnesses below cover tan on the REDUCED interval.
    k = round(float((Fraction(a[0]) + Fraction(a[1])) / 2) / math.pi)
    if k:
        a = (a[0] - k * PI[1], a[1] - k * PI[0]) if k > 0 else (a[0] - k * PI[0], a[1] - k * PI[1])
    if a[1] - a[0] >= PI[0]:
        return None                       # a whole period inside: a pole is a reading, undefined there — a mark
    if a[0] > TAN_EDGE or a[1] < -TAN_EDGE:
        raise FloorLimit("tan is read only at a distance >= pi/2 - 1.5 from its poles")
    if a[0] < -TAN_EDGE or a[1] > TAN_EDGE:
        return None
    r = _iv_mono(tan_pt, a)
    import ztrigcert
    if not ztrigcert.tan_ok(a[0], a[1], r[0], r[1]):
        TRIG_UNCOVERED["tan"] += 1
        return None                       # no Lean witnesses: a mark, not a value
    return r


def _touches(a, centre, period):
    """Can [a0, a1] hold a point centre + k·period (centre, period brackets — pi's)? Sound: True when unsure."""
    lo_k = math.floor((float(a[0]) - float(centre[1])) / float(period[1])) - 1
    hi_k = math.ceil((float(a[1]) - float(centre[0])) / float(period[0])) + 1
    for k in range(lo_k, hi_k + 1):
        ends = [centre[0] + k * period[0], centre[0] + k * period[1], centre[1] + k * period[0],
                centre[1] + k * period[1]]
        if min(ends) <= a[1] and a[0] <= max(ends):
            return True
    return False


def _iv_sc(a, pt, max_at, min_at):
    """sin or cos over [a0, a1]: the ends' brackets, and +-1 where a maximum or a minimum (max_at / min_at + 2pi·k,
    pi bracketed) may lie inside — between such points the function is monotone, so the ends bound it there."""
    if _inf(a[0]) or _inf(a[1]):
        return Fraction(-1), Fraction(1)
    a0, a1 = Fraction(a[0]), Fraction(a[1])
    if a1 - a0 >= TWO_PI[0]:
        return Fraction(-1), Fraction(1)
    p0, p1 = pt(a0), pt(a1)
    lo, hi = min(p0[0], p1[0]), max(p0[1], p1[1])
    if _touches((a0, a1), max_at, TWO_PI):
        hi = Fraction(1)
    if _touches((a0, a1), min_at, TWO_PI):
        lo = Fraction(-1)
    return lo, hi


HALF_PI = (PI[0] / 2, PI[1] / 2)


# EVERY sin / cos / tan reading is checked against the Lean theorems' own witnesses (ztrigcert; lean/ZTrig10-14,
# zero axioms) before it leaves: a side without them is widened to +-1 (tan: no reading) and counted here. So
# a reading this module returns is covered by ZTrig.Ev_cos / Ev_sin / Ev_tan in THIS run, not only on a sample
# (2026-10-17; before, the seam was measured by test_trigcert.py alone). MEASURED: ~6 ms per reading.
TRIG_UNCOVERED = {"sin": 0, "cos": 0, "tan": 0}


def _covered(which, a, r):
    if _inf(a[0]) or _inf(a[1]):
        return r
    import ztrigcert
    lu, hu = Fraction(a[0]), Fraction(a[1])
    lo, hi = r
    if not ztrigcert.side_ok(which, lu, hu, lo, hi, "hi"):
        TRIG_UNCOVERED[which] += 1
        hi = Fraction(1)
    if not ztrigcert.side_ok(which, lu, hu, lo, hi, "lo"):
        TRIG_UNCOVERED[which] += 1
        lo = Fraction(-1)
    return lo, hi


def iv_sin(a):
    return _covered("sin", a, _iv_sc(a, sin_pt, HALF_PI, (-HALF_PI[1], -HALF_PI[0])))


def iv_cos(a):
    return _covered("cos", a, _iv_sc(a, cos_pt, (Fraction(0), Fraction(0)), PI))


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
    # 0 ** y = 0 FOR y > 0 (2026-11-24, found by lean2zfl's reading of a^(7/8) at a = 0): until then a base that may
    # be 0 was a mark and a base pinned at 0 had no readings, though 0 ** (7/8) is 0. For y <= 0 it stays undefined.
    zero_ok = b[0] > 0
    if a[1] <= 0:
        if zero_ok and a[0] == 0 and a[1] == 0 and not is_gap(a[1]):
            return Fraction(0), Fraction(0)
        raise NoReadings("a non-integer power of a quantity that is never positive")
    if a[0] <= 0:
        if not (a[0] == 0 and (is_gap(a[0]) or zero_ok)):
            return None
        a = (gap(0), a[1])                # the positive part; a closed 0 adds the value 0, the low end below
    l = iv_ln(a)
    cands = [x * y for x in l for y in b]
    return iv_exp((min(cands), max(cands)))     # -inf * y (y > 0) -> exp reads 0 at -inf: the 0 of a closed base


def iv_pow_intrange(a, n):
    """a^n for EVERY integer n in [n0, n1] (2026-11-24, step 2 of the Lean reading: `x ^ n` with n a natural variable;
    VR's vpow is repeated multiplication). n0 >= 0 only (a negative range is a mark here). A Python reading: no Lean twin.
      base >= 0: x^n is monotone in x and in n, so the extremes sit at the corners; with n1 = inf the top is inf for a
                 base above 1 and the bottom runs down to 0 for a base below 1 (0 is kept as a closed end: wider, sound);
                 0 ** 0 = 1, as in Lean and in algebra;
      a base that may be negative: the sign follows n's parity, which an interval does not carry — [-M, M] by the
                 magnitude M = max |x|^n, never a guess of the parity."""
    n0, n1 = n
    if n0 == -INF or n0 < 0:
        return None
    n0 = int(math.ceil(n0))
    n1 = INF if _inf(n1) else int(math.floor(n1))
    if n1 != INF and n1 < n0:
        raise NoReadings("an empty range of integer exponents")
    if any(_inf(x) for x in a) and not (a[1] == INF and a[0] >= 0):
        return None
    if a[0] >= 0:
        a0, a1 = Fraction(a[0]), a[1]
        if n1 == INF:
            # the bottom: a0^n0 when the smallest base is >= 1 (x^n grows with n); below 1, x^n runs down to 0
            lo = a0 ** n0 if a0 >= 1 else Fraction(0)
            # the top: unbounded above 1; exactly 1 at a top base of 1; below 1 the largest is at n0 (x^n falls with n)
            if a1 == INF or a1 > 1:
                hi = INF
            elif a1 == 1:
                hi = Fraction(1)
            else:
                hi = Fraction(a1) ** n0              # n0 = 0 gives 1 (0 ** 0 = 1 too)
            return lo, hi
        ends = [a0 ** n0, a0 ** n1] + ([INF] if a1 == INF else [Fraction(a1) ** n0, Fraction(a1) ** n1])
        fin = [e for e in ends if not _inf(e)]
        return min(fin), (INF if a1 == INF and n1 > 0 else max(fin))
    if n1 == INF:
        return None
    m = max(abs(Fraction(a[0])), abs(Fraction(a[1])))
    mag = max(m ** n0, m ** n1)
    return -mag, mag


def iv_min(a, b):
    return min(a[0], b[0]), min(a[1], b[1])


def iv_max(a, b):
    return max(a[0], b[0]), max(a[1], b[1])


def _side(x):
    """+1 when x > 0 everywhere, -1 when x <= 0 everywhere, 0 when the reading does not decide."""
    if x[0] > 0:
        return 1
    if x[1] <= 0:
        return -1
    return 0


def iv_ifpos(x, a, b):
    """A BRANCH (blind test 2, 2026-10-10: Euler or Johnson by slenderness): a where x > 0, b where x <= 0.
    Decided over the whole reading -> that branch; not decided -> the hull of both (every value either
    branch can take): sound, may be wide. a or b may be None when that branch is not needed."""
    s = _side(x)
    if s == 1:
        return a
    if s == -1:
        return b
    if a is None or b is None:
        return None
    return min(a[0], b[0]), max(a[1], b[1])


def iv_ifpos_d(x, a, b):
    """The DERIVATIVE of a branch: only where the branch is decided. Across the switch the function may
    jump, so a sign of 'the derivative' there says nothing about monotonicity: no reading (None)."""
    s = _side(x)
    return a if s == 1 else (b if s == -1 else None)


UNARY = {"exp": iv_exp, "ln": iv_ln, "log10": iv_log10, "atan": iv_atan, "tan": iv_tan, "sin": iv_sin, "cos": iv_cos}
BINARY = {"pow": iv_pow, "min": iv_min, "max": iv_max}
TERNARY = {"ifpos": iv_ifpos, "ifpos_d": iv_ifpos_d}
# BESSEL AND KELVIN (2026-11-09, zseries): besselj0 besselj1 ber bei berp beip and their derivatives to order 8,
# each a proved bracket from its alternating series (zseries.py; no Lean witnesses yet, said there).
import zseries as _ZS                                                               # noqa: E402
for _b in _ZS.FAMILIES:
    for _n in range(9):
        _nm = _b if _n == 0 else f"{_b}_d{_n}"
        UNARY[_nm] = _ZS.unary(_nm)
for _a in _ZS.ALIASES:
    UNARY[_a] = _ZS.unary(_a)
# THE INTEGER WORDS (2026-11-24, step 3: the twin of VR/Numbers/Division.lean, every object there on []):
# idiv, mod (Euclidean, divisor >= 1), dvd (1 when a | b: some k with a*k = b, else 0), fact, choose. Read on the
# INTEGER LATTICE only (znum checks it); no convention value: a divisor 0 is not a value that was chosen — VR cannot
# even write it (the divisor is succ d by construction) — so idiv/mod by a pinned 0 has NO reading (E). 0 | 0 holds and
# 0 | b (b != 0) fails BY THE DEFINITION (a witness k), and choose(n, k) = 0 for k > n is the count of k-subsets
# (proved in VR: vchoose_eq_base_of_lt). VR's words are on the naturals: a negative argument of idiv/mod/fact/choose
# exists in Z but is not read by this twin (FloorLimit, a mark); dvd reads Z by magnitudes (a | b iff |a| | |b|).
INTWORDS = {"idiv": 2, "mod": 2, "dvd": 2, "fact": 1, "choose": 2}
INT_ENUM_CAP = 4096          # a range of integer arguments is read point by point up to this many points
FACT_CAP = 2000              # n! past this n is not read by the floor (FloorLimit): it exists, it is just huge


def _ipts(a):
    """the integers of an interval [a0, a1] (finite ends), as a range"""
    return range(int(math.ceil(a[0])), int(math.floor(a[1])) + 1)


def _enum(f, *ivs):
    """min/max of f over every integer point of the boxes, when there are few enough; else None (a mark)"""
    if any(_inf(x) for iv in ivs for x in iv):
        return None
    n = 1
    for iv in ivs:
        n *= max(0, int(math.floor(iv[1])) - int(math.ceil(iv[0])) + 1)
    if n == 0:
        raise NoReadings("no integer reading in the range")
    if n > INT_ENUM_CAP:
        return None
    import itertools
    vals = [f(*pt) for pt in itertools.product(*[_ipts(iv) for iv in ivs])]
    return Fraction(min(vals)), Fraction(max(vals))


def _nat_args(name, *ivs):
    for iv in ivs:
        if iv[1] < 0:
            raise FloorLimit(f"{name} of a negative integer: it exists in Z, the VR twin reads the naturals")
        if iv[0] < 0:
            return False
    return True


def iv_idiv(a, b):
    if b[0] == 0 and b[1] == 0:
        raise NoReadings("idiv by 0: no value (VR's divisor is succ d — the division cannot be written)")
    if not _nat_args("idiv", a, b):
        return None
    if b[0] == 0:
        return None                                          # 0 is a reading of the divisor: undefined there — a mark
    lo = Fraction(0) if _inf(b[1]) else Fraction(int(math.floor(a[0])) // int(math.floor(b[1])))
    hi = INF if _inf(a[1]) else Fraction(int(math.floor(a[1])) // int(math.ceil(b[0])))
    return lo, hi                                            # monotone: up in a, down in b (a >= 0, b >= 1)


def iv_mod(a, b):
    if b[0] == 0 and b[1] == 0:
        raise NoReadings("mod by 0: no value (VR's divisor is succ d — the division cannot be written)")
    if not _nat_args("mod", a, b):
        return None
    if b[0] == 0:
        return None
    r = _enum(lambda x, y: x % y, a, b)
    if r is not None:
        return r
    top = (b[1] - 1) if not _inf(b[1]) else INF
    top = a[1] if (_inf(top) or (not _inf(a[1]) and a[1] < top)) else top
    return Fraction(0), (top if _inf(top) else Fraction(int(math.floor(top))))


def _dvd_pt(x, y):
    x, y = abs(x), abs(y)
    return 1 if (y == 0 if x == 0 else y % x == 0) else 0


def iv_dvd(a, b):
    r = _enum(_dvd_pt, a, b)
    return r if r is not None else (Fraction(0), Fraction(1))


def iv_fact(n):
    if not _nat_args("fact", n):
        return None
    if _inf(n[1]):
        return Fraction(math.factorial(int(math.ceil(n[0])))), INF
    if n[1] > FACT_CAP:
        raise FloorLimit(f"fact of n > {FACT_CAP} is not read by the floor")
    return (Fraction(math.factorial(int(math.ceil(n[0])))), Fraction(math.factorial(int(math.floor(n[1])))))


def _choose_pt(n, k):
    return math.comb(n, k) if 0 <= k <= n else 0


def iv_choose(n, k):
    if not _nat_args("choose", n, k):
        return None
    if not _inf(n[1]) and n[1] > FACT_CAP:
        raise FloorLimit(f"choose of n > {FACT_CAP} is not read by the floor")
    return _enum(_choose_pt, n, k)


# MORE INTEGER WORDS (2026-11-25, the curator's "делаем": lean2zfl's Lean Workbook statements use Nat.gcd, lcm, fib,
# totient, Prime). A Python reading: VR's Division twin covers idiv mod dvd fact choose only. On the integer lattice,
# read point by point (_enum) over a small range, else a mark — except fib, monotone on the naturals.
#   gcd(a, b), lcm(a, b) by magnitudes; gcd(0, 0) = 0, lcm(a, 0) = 0 (the divisibility lattice's own meet and join)
#   fib(0) = 0, fib(1) = 1;  totient(n) = #{1 <= k <= n : gcd(k, n) = 1} (0 at n = 0: the empty count)
#   isprime(n) = 1 when n has exactly two divisors in N, else 0
FIB_CAP = 20000


def _fib_pt(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def _totient_pt(n):
    if n <= 0:
        return 0
    out, m, p = n, n, 2
    while p * p <= m:
        if m % p == 0:
            while m % p == 0:
                m //= p
            out -= out // p
        p += 1
    if m > 1:
        out -= out // m
    return out


def _isprime_pt(n):
    if n < 2:
        return 0
    p = 2
    while p * p <= n:
        if n % p == 0:
            return 0
        p += 1
    return 1


def iv_gcd(a, b):
    return _enum(lambda x, y: math.gcd(abs(x), abs(y)), a, b)


def iv_lcm(a, b):
    return _enum(lambda x, y: abs(x * y) // math.gcd(abs(x), abs(y)) if x and y else 0, a, b)


def iv_fib(n):
    if not _nat_args("fib", n):
        return None
    if not _inf(n[1]) and n[1] > FIB_CAP:
        raise FloorLimit(f"fib of n > {FIB_CAP} is not read by the floor")
    lo = Fraction(_fib_pt(int(math.ceil(n[0]))))
    return lo, (INF if _inf(n[1]) else Fraction(_fib_pt(int(math.floor(n[1])))))


def iv_totient(n):
    if not _nat_args("totient", n):
        return None
    if not _inf(n[1]) and n[1] > 10 ** 12:
        raise FloorLimit("totient past 10^12 is not read by the floor")
    return _enum(_totient_pt, n)


def iv_isprime(n):
    if not _inf(n[1]) and n[1] > 10 ** 12:
        raise FloorLimit("isprime past 10^12 is not read by the floor")
    r = _enum(_isprime_pt, n)
    return r if r is not None else (Fraction(0), Fraction(1))


INTWORDS.update({"gcd": 2, "lcm": 2, "fib": 1, "totient": 1, "isprime": 1})
INTFUNCS = {"idiv": iv_idiv, "mod": iv_mod, "dvd": iv_dvd, "fact": iv_fact, "choose": iv_choose,
            "gcd": iv_gcd, "lcm": iv_lcm, "fib": iv_fib, "totient": iv_totient, "isprime": iv_isprime}


# ⌊x⌋, ⌈x⌉ of a REAL (2026-11-25): monotone, so the ends' floors bound it (an excluded end read closed: a superset)
def iv_floor(x):
    import zgap
    hi = x[1] if _inf(x[1]) else Fraction(math.floor(x[1]))
    if zgap.is_gap(x[1]) and Fraction(x[1]).denominator == 1:
        hi = hi - 1                                      # [2, 3): every reading is below 3, so its floor is <= 2
    return (x[0] if _inf(x[0]) else Fraction(math.floor(x[0])), hi)


def iv_ceil(x):
    import zgap
    lo = x[0] if _inf(x[0]) else Fraction(math.ceil(x[0]))
    if zgap.is_gap(x[0]) and Fraction(x[0]).denominator == 1:
        lo = lo + 1                                      # (2, 3]: every reading is above 2, so its ceiling is >= 3
    return (lo, x[1] if _inf(x[1]) else Fraction(math.ceil(x[1])))


UNARY["floor"] = iv_floor
UNARY["ceil"] = iv_ceil
FUNC_OPS = set(UNARY) | set(BINARY) | set(TERNARY) | set(INTWORDS)
