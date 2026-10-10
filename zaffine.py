# -*- coding: utf-8 -*-
"""
AFFINE READING — an interval reading that remembers WHICH input a spread came from.

WHY (2026-10-10, the universal stand's blind test 2, the oil cooler): the eps-NTU law has NTU in the
numerator and in the denominator; plain interval arithmetic reads the two as independent, and over a
2 K slice of the outlet temperature g read [-55.8, +11.1] where its true values are all negative — the
heat exchanger that passes stayed OPEN. That is the textbook DEPENDENCY problem, and affine arithmetic
is its textbook cure (Comba & Stolfi 1993; de Figueiredo & Stolfi 2004).

A quantity is   x0 + sum_i x_i * e_i + [-err, +err],   each e_i in [-1, 1] one INPUT of the box.
Linear operations are exact. A nonlinear one is replaced by its best linear stand-in plus a PROVED
remainder that goes into err (the min-range rule: for f monotone with monotone f', take the slope at the
end where it is smaller, so the remainder f - alpha*y is monotone and its range is read at the two ends,
with zfunc's proved brackets). Products add rad(x)*rad(y) to err. Everything is exact fractions; the
coefficients are kept on a relative 2^-80 grid, the rounding added to err — so it stays sound and small.

The result is INTERSECTED with the plain reading (both are enclosures), so it is never worse. Anything this
file does not know (min, max, a branch, a sum over a list, an infinite end) is read plainly and enters as
ONE new independent input: sound, it only forgets that subtree's correlations.
"""

from fractions import Fraction
import math

import zfunc as ZF

GRID = 80


def _down(x):
    return ZF._down(Fraction(x), GRID)


def _up(x):
    return ZF._up(Fraction(x), GRID)


class Unknown(Exception):
    """This file cannot read the node affinely; the caller falls back to the plain reading."""


class Aff:
    __slots__ = ("c", "t", "e")

    def __init__(self, c, t=None, e=Fraction(0)):
        self.c, self.t, self.e = Fraction(c), dict(t or {}), Fraction(e)

    def rad(self):
        return sum((abs(v) for v in self.t.values()), Fraction(0)) + self.e

    def iv(self):
        r = self.rad()
        return self.c - r, self.c + r

    def tidy(self):
        """Coefficients onto the grid; what rounding moved goes into err (outward)."""
        e = self.e
        t = {}
        for k, v in self.t.items():
            if v == 0:
                continue
            w = _down(v) if v > 0 else -_down(-v)
            e += abs(v - w)
            if w != 0:
                t[k] = w
        c = self.c
        w = _down(c) if c >= 0 else -_down(-c)
        e += abs(c - w)
        self.c, self.t, self.e = w, t, _up(e)
        return self


def _add(x, y, s=1):
    t = dict(x.t)
    for k, v in y.t.items():
        t[k] = t.get(k, 0) + s * v
    return Aff(x.c + s * y.c, t, x.e + y.e)


def _mul(x, y):
    t = {}
    for k, v in x.t.items():
        t[k] = t.get(k, 0) + y.c * v
    for k, v in y.t.items():
        t[k] = t.get(k, 0) + x.c * v
    rx = sum((abs(v) for v in x.t.values()), Fraction(0))
    ry = sum((abs(v) for v in y.t.values()), Fraction(0))
    e = abs(x.c) * y.e + abs(y.c) * x.e + (rx + x.e) * (ry + y.e)
    return Aff(x.c * y.c, t, e).tidy()


def _scale(x, a, b=Fraction(0), extra=Fraction(0)):
    """a*x + b, err += extra."""
    return Aff(a * x.c + b, {k: a * v for k, v in x.t.items()}, abs(a) * x.e + extra).tidy()


def _minrange(x, f, df, convex, end):
    """f(x) for f monotone with f' monotone on x's interval [a, b]: f ~ alpha*x + zeta +- delta.
    f(t), df(t) -> proved (lo, hi) brackets of f(t), f'(t). The slope is taken at `end` and rounded so the
    remainder r = f - alpha*y is MONOTONE on [a, b]; r's range is then read at the two ends:
        convex (f' increasing): end a -> alpha <= f'(a), r increasing;  end b -> alpha >= f'(b), r decreasing
        concave (f' decreasing): end a -> alpha >= f'(a), r decreasing; end b -> alpha <= f'(b), r increasing"""
    a, b = x.iv()
    fa, fb = f(a), f(b)
    if convex and end == "a":
        alpha, inc = _down(df(a)[0]), True
    elif convex:
        alpha, inc = _up(df(b)[1]), False
    elif end == "a":
        alpha, inc = _up(df(a)[1]), False
    else:
        alpha, inc = _down(df(b)[0]), True
    ra = (fa[0] - alpha * a, fa[1] - alpha * a)
    rb = (fb[0] - alpha * b, fb[1] - alpha * b)
    rlo, rhi = (ra[0], rb[1]) if inc else (rb[0], ra[1])
    zeta, delta = (rlo + rhi) / 2, (rhi - rlo) / 2
    return _scale(x, alpha, zeta, _up(delta))


def _pick_end(da, db):
    return "a" if max(abs(da[0]), abs(da[1])) <= max(abs(db[0]), abs(db[1])) else "b"


def _recip(x):
    a, b = x.iv()
    if a <= 0 <= b:
        raise Unknown("1/x across zero")
    f = lambda t: (1 / Fraction(t), 1 / Fraction(t))
    df = lambda t: (-1 / (Fraction(t) * t), -1 / (Fraction(t) * t))
    convex = a > 0                                    # 1/x is convex for x > 0, concave for x < 0
    return _minrange(x, f, df, convex, _pick_end(df(a), df(b)))


def _exp(x):
    a, b = x.iv()
    f = lambda t: ZF.exp_pt(Fraction(t))
    return _minrange(x, f, f, True, "a")


def _ln(x):
    a, b = x.iv()
    if a <= 0:
        raise Unknown("ln reaching zero")
    f = lambda t: ZF.ln_pt(Fraction(t))
    df = lambda t: (1 / Fraction(t), 1 / Fraction(t))
    return _minrange(x, f, df, False, "b")


def _sqrt(x, rat_sqrt):
    a, b = x.iv()
    if a <= 0:
        raise Unknown("sqrt reaching zero")
    f = lambda t: rat_sqrt(Fraction(t))
    df = lambda t: (1 / (2 * rat_sqrt(Fraction(t))[1]), 1 / (2 * rat_sqrt(Fraction(t))[0]))
    return _minrange(x, f, df, False, "b")


def _atan(x):
    a, b = x.iv()
    if a < 0 < b:
        raise Unknown("atan across zero (its curvature changes sign)")
    f = lambda t: ZF.atan_pt(Fraction(t))
    df = lambda t: (1 / (1 + Fraction(t) * t), 1 / (1 + Fraction(t) * t))
    convex = b <= 0
    return _minrange(x, f, df, convex, _pick_end(df(a), df(b)))


def read(e, qs, piece, rat_sqrt, plain):
    """(lo, hi) — the affine reading of reader node e over the box (qs with piece's ranges), or None.
    plain(node) -> the caller's plain reading of a subtree (used for nodes this file does not linearise)."""
    def leaf(name):
        lo, hi = piece.get(name, (qs[name]["lo"], qs[name]["hi"]))
        if isinstance(lo, float) or isinstance(hi, float):
            raise Unknown("an infinite end")
        lo, hi = Fraction(lo), Fraction(hi)
        if lo == hi:
            return Aff(lo)
        return Aff((lo + hi) / 2, {name: (hi - lo) / 2})

    fresh = [0]

    def opaque(n):
        """A subtree read plainly: ONE new independent input (sound; forgets only its own correlations)."""
        iv = plain(n)
        if iv is None or any(isinstance(v, float) for v in iv):
            raise Unknown("no plain reading")
        lo, hi = Fraction(iv[0]), Fraction(iv[1])
        fresh[0] += 1
        return Aff((lo + hi) / 2, {("#", fresh[0]): (hi - lo) / 2} if lo != hi else {})

    def ev(n):
        if isinstance(n, (int, Fraction)):
            return Aff(Fraction(n))
        if isinstance(n, str):
            return leaf(n)
        op, *args = n
        try:
            if op == "add":
                return _add(ev(args[0]), ev(args[1]))
            if op == "sub":
                return _add(ev(args[0]), ev(args[1]), -1)
            if op == "mul":
                return _mul(ev(args[0]), ev(args[1]))
            if op == "div":
                return _mul(ev(args[0]), _recip(ev(args[1])))
            if op == "exp":
                return _exp(ev(args[0]))
            if op == "ln":
                return _ln(ev(args[0]))
            if op == "log10":
                ln10 = ZF.LN10
                return _mul(_ln(ev(args[0])), _recip(Aff((ln10[0] + ln10[1]) / 2, {}, (ln10[1] - ln10[0]) / 2)))
            if op == "sqrt":
                return _sqrt(ev(args[0]), rat_sqrt)
            if op == "atan":
                return _atan(ev(args[0]))
            if op == "pow":
                base, ex = args
                if isinstance(ex, (int, Fraction)) and Fraction(ex).denominator == 1:
                    k = int(ex)
                    if k == 0:
                        return Aff(1)
                    x = ev(base)
                    out = x
                    for _ in range(abs(k) - 1):
                        out = _mul(out, x)
                    return _recip(out) if k < 0 else out
                return _exp(_mul(ev(ex), _ln(ev(base))))
        except Unknown:
            pass
        return opaque(n)                     # min, max, a branch, a sum, tan, or a failed linearisation

    try:
        out = ev(e)
    except (Unknown, ZeroDivisionError, ZF.NoReadings, ValueError, OverflowError, TypeError):
        return None
    return out.iv()
