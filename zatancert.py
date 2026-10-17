"""ATAN AT A RATIONAL POINT, CERTIFIED AS LEAN DOES (lean/ZAtanCert.lean) — a Taylor chain from atan 0 = 0.

Lean's atan (lean/ZAtan.lean `atseq`) is the grid sum of 1/(1 + t²); the kernel reads it through brackets from series
(zfunc.atan_pt). VRead.atan takes the values at the ends of its argument's reading as facts about two rational points;
this file produces them the way ZAtanCert.atan_step proves them:
  * atan 0 = 0 exactly;
  * one step x0 → x1: the kernel's series of atan(x) (CRead.atan over var 0: U = a∗a + 1, Dd_t = (t+1)·a_{t+1},
    w_0 = Dd_0/U_0, w_{j+1} = (Dd_{j+1} − (w ∗ U')_j)/U_0, c_{t+1} = w_t/(t+1); the value coefficient the crude
    |atan y| ≤ |y|) over the point box [x0, x0] for the coefficients t ≥ 1 and over [x0, x1] for the remainder:
    atan x1 ∈ Σ_{t<m} P_t·d^t + c_m·d^m, P_0 the chain's previous reading, every product by corners;
  * the steps grow with |x| (the series' radius at t is √(1 + t²)): dyadic points, a step at most max(1/16, |t|/16).
Exact arithmetic throughout; each reading rounded outward to a 2^-90 grid (Lean: Hull, a wider P_0 is allowed).
"""
from fractions import Fraction as F
import math

ORDER = 26                      # MEASURED 2026-10-17: steps max(1/16, |t|/16), order 26 -> width ~2^-80 at
                                # x = 1, 10, 1000 (step 1/4, order 30: 2^-44 .. 2^-24, the box remainder over-read)
_GRID = 2 ** 90
_CACHE = {F(0): (F(0), F(0))}


def _corners(a, b):
    ps = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return min(ps), max(ps)


def _cvb(A, B, m):
    lo = hi = F(0)
    for j in range(m + 1):
        l, h = _corners(A[j], B[m - j])
        lo, hi = lo + l, hi + h
    return lo, hi


def _out(iv, bits=110):
    """Round an interval outward to `bits` significant bits (Lean: Hull — a wider coefficient is admitted)."""
    l, h = iv
    mag = max(abs(l), abs(h))
    if mag == 0:
        return iv
    e = math.floor(math.log2(mag)) - bits
    g = F(2) ** e
    return F(math.floor(l / g)) * g, F(math.ceil(h / g)) * g


def series(lo, hi, m=ORDER):
    """CRead.atan of atan(var 0) over [lo, hi] to order m (the tightest coefficients Lean's rule admits)."""
    lo, hi = F(lo), F(hi)
    Y = max(abs(lo), abs(hi))
    a = [(lo, hi), (F(1), F(1))] + [(F(0), F(0))] * m
    U = []
    for s in range(m):
        l, h = _cvb(a, a, s)
        u = F(1) if s == 0 else F(0)
        U.append((u + l, u + h))
    if m == 0:
        return [(-Y, Y)]
    r = (F(1) / U[0][1], F(1) / U[0][0])
    Dd = [_corners((F(t + 1), F(t + 1)), a[t + 1]) for t in range(m)]
    r = _out(r)
    w = [_out(_corners(Dd[0], r))]
    for j in range(m - 1):
        cl, ch = _cvb(w, [U[s + 1] if s + 1 < m else (F(0), F(0)) for s in range(j + 1)], j)
        w.append(_out(_corners((Dd[j + 1][0] - ch, Dd[j + 1][1] - cl), r)))
    return [(-Y, Y)] + [_out(_corners(w[t], (F(1, t + 1), F(1, t + 1)))) for t in range(m)]


def step(x0, x1, L, H, m=ORDER):
    """atan_step: a reading [L, H] of atan x0 carried to one of atan x1."""
    x0, x1 = F(x0), F(x1)
    cB = series(min(x0, x1), max(x0, x1), m)
    cP = series(x0, x0, m)
    d = x1 - x0
    lo, hi = F(0), F(0)
    for t in range(m):
        P = (L, H) if t == 0 else cP[t]
        l, h = _corners(P, (d ** t, d ** t))
        lo, hi = lo + l, hi + h
    l, h = _corners(cB[m], (d ** m, d ** m))
    return lo + l, hi + h


def _round(L, H):
    return F(math.floor(L * _GRID), _GRID), F(math.ceil(H * _GRID), _GRID)


def _dyadic_step(t):
    s = max(F(1, 16), abs(t) / 16)
    return F(2) ** math.floor(math.log2(s))


def _next(t, x, sg):
    """The next chain point: the dyadic step from t, aligned to its own grid, or x itself."""
    d = _dyadic_step(t)
    nxt = (math.floor(t / d) + 1) * d if sg > 0 else (math.ceil(t / d) - 1) * d
    return x if (nxt - x) * sg >= 0 else F(nxt)


def atan_cert(x):
    """[L, H] with atan x in it, as Lean certifies it (cached)."""
    x = F(x)
    if x in _CACHE:
        return _CACHE[x]
    # start from the certified point nearest to x (0 is always one: atan 0 = 0)
    t = min(_CACHE, key=lambda c: abs(c - x))
    L, H = _CACHE[t]
    sg = 1 if x > t else -1
    while t != x:
        nxt = _next(t, x, sg)
        L, H = _round(*step(t, nxt, L, H))
        t = nxt
        if t not in _CACHE and t.denominator & (t.denominator - 1) == 0:
            _CACHE[t] = (L, H)          # chain points are dyadic: kept as later starts
    _CACHE[x] = (L, H)
    return L, H
