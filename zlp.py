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


def _qs_for(qs_con, i):
    """One box for every constraint, or one per constraint (each mode its own data: 2026-10-10)."""
    return qs_con[i] if isinstance(qs_con, list) else qs_con


def _remainders(constraints, qs_con, xs, ys, points):
    """[(y, h0, hx)] — each constraint as a remainder h = g - b >= 0 (or b - g), affine in xs, read by the
    kernel (at its point, when one is given and lies in the box). Raises NotAffine / ValueError."""
    points = points or [None] * len(constraints)
    if len(points) != len(constraints):
        raise ValueError("one point (or none) per constraint")
    out = []
    for i, ((node, op, bound), y, pt) in enumerate(zip(constraints, ys, points)):
        if y == 0:
            continue
        q = _qs_for(qs_con, i)
        piece = {}
        for n, v in (pt or {}).items():
            v = Fraction(str(v))
            if n not in q or n in xs or not (q[n]["lo"] <= v <= q[n]["hi"]):
                raise ValueError(f"the point's {n} = {v} is not inside its box")
            piece[n] = (v, v)
        d0, dx = affine(node, xs, q, piece)
        b = Fraction(str(bound))
        if op == ">=":
            out.append((y, (d0[0] - b, d0[1] - b), dx))
        elif op == "<=":
            out.append((y, (b - d0[1], b - d0[0]), {x: (-v[1], -v[0]) for x, v in dx.items()}))
        else:
            raise ValueError(f"op {op!r}")
    return out


def infeasible(constraints, qs_con, xs, ys, points=None):
    """(True, M) when NO x in the box meets every constraint for every value of the data — a FARKAS certificate:
    with y >= 0, the box-MAXIMUM M of sum y_i h_i(x) is below zero, while a feasible x would make it >= 0.
    (False, reason) otherwise. Blind test 3: "the robust LP found no mix" was reported as no proof at all."""
    if len(ys) != len(constraints):
        return False, "one multiplier per constraint"
    try:
        ys = [Fraction(str(y)) for y in ys]
    except (ValueError, ZeroDivisionError, TypeError):
        return False, "a multiplier is not a number"
    if any(y < 0 for y in ys) or not any(y > 0 for y in ys):
        return False, "multipliers must be >= 0 and not all zero"
    for x, (lo, hi) in xs.items():
        if isinstance(lo, float) or isinstance(hi, float) or lo > hi:
            return False, f"{x}: an infinite or empty range"
    try:
        terms = _remainders(constraints, qs_con, xs, ys, points)
    except (NotAffine, ValueError) as e:
        return False, str(e)
    s0 = (Fraction(0), Fraction(0))
    sx = {}
    for y, h0, hx in terms:
        s0 = (s0[0] + y * h0[0], s0[1] + y * h0[1])
        for x, v in hx.items():
            a = sx.get(x, (Fraction(0), Fraction(0)))
            sx[x] = (a[0] + y * v[0], a[1] + y * v[1])
    M = s0[1]
    for x, (lo, hi) in xs.items():
        M += _mul_iv(sx.get(x, (Fraction(0), Fraction(0))), (lo, hi))[1]
    return (True, M) if M < 0 else (False, f"the box-maximum of sum y*h is {M}, not below zero")


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
        terms = _remainders(constraints, qs_con, xs, ys, points)
    except NotAffine as e:
        return False, f"not affine: {e}"
    except ValueError as e:
        return False, str(e)
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
