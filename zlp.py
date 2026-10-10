# -*- coding: utf-8 -*-
"""
A LOWER BOUND ON A LINEAR OPTIMUM, CHECKED — weak LP duality over a box of uncertain coefficients.

WHY (2026-10-10, the universal stand's blind test 3): a feed formula and a concrete mix choose CONTINUOUS
amounts; the stand verified the candidates an LP outside proposed, but "no cheaper mix exists" rested on that
LP alone. Weak duality makes the claim checkable: for any multipliers y >= 0,

    objective(x)  >=  objective(x) - sum_i y_i * h_i(x, p)        for every x feasible (h_i(x, p) >= 0 for all p)
                  >=  min over the box of x and p of the right side  =:  L

and the right side is AFFINE in x, so its minimum over a box of x is read end by end. The search (an LP solver,
outside) only proposes y; the kernel needs nothing from it to be right: ANY y >= 0 gives a sound L, a good y
gives a tight one. The kernel does not take the LP's matrix on trust either: it derives every coefficient from
the expressions themselves (zcertify.derivative) and checks each expression is affine in x (no partial
derivative contains an x). No budget, no rounding: exact fractions over the kernel's readings.
"""

from fractions import Fraction

import zcertify as ZC


class NotAffine(ValueError):
    pass


def affine(node, xs, qs, piece=None):
    """(const (lo, hi), {x: (lo, hi)}) — node = const + sum coef_x * x over the box, or NotAffine."""
    piece = dict(piece or {})
    coefs = {}
    for x in xs:
        try:
            d = ZC.derivative(node, x)
        except ZC.NoDerivative as e:
            raise NotAffine(f"{x}: {e}")
        if ZC._names(d) & set(xs):
            raise NotAffine(f"the coefficient of {x} depends on {sorted(ZC._names(d) & set(xs))}: not affine")
        r = ZC._reading(d, qs, piece)
        if r is None:
            raise NotAffine(f"the coefficient of {x} has no reading over the box")
        coefs[x] = r
    zero = dict(piece, **{x: (Fraction(0), Fraction(0)) for x in xs})
    c = ZC._reading(node, qs, zero)
    if c is None:
        raise NotAffine("the constant term has no reading over the box")
    return c, coefs


def _mul_iv(a, b):
    ps = [a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1]]
    return min(ps), max(ps)


def lower_bound(objective, qs_obj, constraints, qs_con, xs, ys, points=None):
    """(True, L) or (False, reason).
    objective: a reader node to MINIMISE, read over qs_obj (e.g. at nominal prices: points).
    constraints: [(node, op, bound)] with op ">=" or "<=", each required for EVERY value of qs_con's box.
    xs: {x: (lo, hi)} the continuous choices (finite). ys: one multiplier >= 0 per constraint.
    points: optional, one {parameter: value} per constraint — the constraint holds for EVERY value of the box,
    so it may be read at any one point of it (the certificate names the hardest; the kernel checks it lies in
    the box). Without a point the constraint's coefficients are read as intervals over the whole box (sound,
    weaker: L = 20/9 against the optimum 70/27 on a two-ingredient diet)."""
    if len(ys) != len(constraints):
        return False, "one multiplier per constraint"
    try:
        ys = [Fraction(str(y)) for y in ys]
    except (ValueError, ZeroDivisionError, TypeError):
        return False, "a multiplier is not a number"
    if any(y < 0 for y in ys):
        return False, "a multiplier is negative"
    for x, (lo, hi) in xs.items():
        if isinstance(lo, float) or isinstance(hi, float) or lo > hi:
            return False, f"{x}: an infinite or empty range"
    try:
        c0, cx = affine(objective, xs, qs_obj)
        terms = []
        points = points or [None] * len(constraints)
        if len(points) != len(constraints):
            return False, "one point (or none) per constraint"
        for (node, op, bound), y, pt in zip(constraints, ys, points):
            if y == 0:
                continue
            piece = {}
            for n, v in (pt or {}).items():
                v = Fraction(str(v))
                if n not in qs_con or n in xs or not (qs_con[n]["lo"] <= v <= qs_con[n]["hi"]):
                    return False, f"the point's {n} = {v} is not inside its box"
                piece[n] = (v, v)
            d0, dx = affine(node, xs, qs_con, piece)
            b = Fraction(str(bound))
            if op == ">=":          # h = g - b >= 0
                h0, hx = (d0[0] - b, d0[1] - b), dx
            elif op == "<=":        # h = b - g >= 0
                h0, hx = (b - d0[1], b - d0[0]), {x: (-v[1], -v[0]) for x, v in dx.items()}
            else:
                return False, f"op {op!r}"
            terms.append((y, h0, hx))
    except NotAffine as e:
        return False, f"not affine: {e}"
    # e = objective - sum y_i h_i : affine with interval coefficients
    e0 = c0
    ex = dict(cx)
    for y, h0, hx in terms:
        e0 = (e0[0] - y * h0[1], e0[1] - y * h0[0])
        for x, v in hx.items():
            a = ex.get(x, (Fraction(0), Fraction(0)))
            ex[x] = (a[0] - y * v[1], a[1] - y * v[0])
    L = e0[0]
    for x, (lo, hi) in xs.items():
        L += _mul_iv(ex.get(x, (Fraction(0), Fraction(0))), (lo, hi))[0]
    return True, L
