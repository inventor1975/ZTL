# -*- coding: utf-8 -*-
"""
CHECKING A BROUGHT CERTIFICATE — a bound over a box, proved by someone else, checked here.

THE DECISION (the curator, 2026-10-09): the kernel takes no budgets. "A budget
spends determinism: without one the instrument is weak but true; with one it gives
an intermediate result." So the SEARCH — splitting a box until every piece is
decided — lives outside (the stand, an agent); it brings a certificate, and the
kernel CHECKS it: exactly (fractions), with no budget, at a cost that follows the
certificate's size. A searcher that finds nothing brings nothing; the kernel never
sees it. Zero trust in the searcher: only what checks counts.

WHAT IS CERTIFIED (first tranche): `E <= c` or `E >= c` for an arithmetic
expression E of boxed quantities (+ - * / sum sqrt), over their whole box.

THE CERTIFICATE is a bisection tree over the box:
    {"split": name, "at": "p/q", "lo": tree, "hi": tree}   the box cut at name = at
    {"leaf": "monotone", "signs": {name: "+" | "-"}}       on this piece E is
                                                           non-decreasing (+) or
                                                           non-increasing (-) in each
                                                           listed name; its extreme
                                                           is then ONE corner
    {"leaf": "interval"}                                   E's interval reading on
                                                           the piece settles it
The tree covers the box by construction (each split halves a piece at a point
inside it). For a monotone leaf the kernel builds dE/dname ITSELF (symbolically),
reads it over the piece, and accepts "+" only if the reading is >= 0 (and "-" only
if <= 0); every quantity of non-zero width on the piece must carry a sign. Then E
is evaluated at the one corner the signs point to. An interval leaf is accepted
when E's interval reading on the piece is on the right side of c.

The answer is True with the number of pieces, or False with the first reason —
deterministic, never "not computed".
"""

import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from znum import _ev                               # noqa: E402

ZERO, ONE = Fraction(0), Fraction(1)


def _is0(e):
    return isinstance(e, Fraction) and e == 0


def _add(a, b):
    if _is0(a):
        return b
    if _is0(b):
        return a
    return ("add", a, b)


def _sub(a, b):
    if _is0(b):
        return a
    return ("sub", a, b)


def _mul(a, b):
    if _is0(a) or _is0(b):
        return ZERO
    if isinstance(a, Fraction) and a == 1:
        return b
    if isinstance(b, Fraction) and b == 1:
        return a
    return ("mul", a, b)


def derivative(e, name):
    """dE/dname, symbolically, over the reader's nodes."""
    if isinstance(e, (int, Fraction)):
        return ZERO
    if isinstance(e, str):
        return ONE if e == name else ZERO
    op, *args = e
    if op == "sum":
        out = ZERO
        for a in args[0]:
            out = _add(out, derivative(a, name))
        return out
    if op == "sqrt":
        u = args[0]
        return ("div", derivative(u, name), ("mul", Fraction(2), ("sqrt", u)))
    a, b = args
    da, db = derivative(a, name), derivative(b, name)
    if op == "add":
        return _add(da, db)
    if op == "sub":
        return _sub(da, db) if not _is0(da) else (("sub", ZERO, db) if not _is0(db) else ZERO)
    if op == "mul":
        return _add(_mul(da, b), _mul(a, db))
    if op == "div":
        if _is0(db):
            return ("div", da, b) if not _is0(da) else ZERO
        return ("div", _sub(_mul(da, b), _mul(a, db)), ("mul", b, b))
    raise ValueError(f"cannot differentiate {op!r}")


def _names(e, acc=None):
    acc = set() if acc is None else acc
    if isinstance(e, str):
        acc.add(e)
    elif isinstance(e, tuple):
        for a in e[1:]:
            if isinstance(a, list):
                for x in a:
                    _names(x, acc)
            else:
                _names(a, acc)
    return acc


def _reading(e, qs, piece):
    """E's interval over the piece (each name's box replaced), or None."""
    q2 = dict(qs)
    for n, (lo, hi) in piece.items():
        q2[n] = dict(qs[n], lo=lo, hi=hi)
    try:
        iv = _ev(e, q2)[0]
    except (ZeroDivisionError, KeyError, ValueError, ArithmeticError):
        return None
    if iv is None:
        return None
    lo, hi = iv
    if isinstance(lo, float) or isinstance(hi, float):
        return None           # an infinite end: nothing certified from it
    return lo, hi


def check(expr, quantities, op, bound, cert):
    """Is `expr op bound` true over the quantities' whole box, by this certificate?
    `expr` a reader node (znumjudge._parse_arith), `op` "<=" or ">=", `bound` a
    Fraction. Returns (True, pieces) or (False, reason)."""
    if op not in ("<=", ">="):
        return False, f"op {op!r}: only <= and >= are certified"
    names = sorted(n for n in _names(expr) if n in quantities)
    box = {n: (quantities[n]["lo"], quantities[n]["hi"]) for n in names}
    for n, (lo, hi) in box.items():
        if isinstance(lo, float) or isinstance(hi, float):
            return False, f"{n} is unbounded: no certificate covers an infinite box"
    derivs = {}
    count = [0]

    def walk(node, piece, path):
        if not isinstance(node, dict):
            return False, f"{path}: not a tree node"
        if "split" in node:
            n = node["split"]
            if n not in piece:
                return False, f"{path}: split on {n!r}, not a quantity of the expression"
            try:
                at = Fraction(str(node["at"]))
            except (ValueError, ZeroDivisionError, KeyError):
                return False, f"{path}: split point unreadable"
            lo, hi = piece[n]
            if not (lo < at < hi):
                return False, f"{path}: split {n} at {at} is not inside [{lo}, {hi}]"
            left, right = dict(piece), dict(piece)
            left[n], right[n] = (lo, at), (at, hi)
            ok, why = walk(node.get("lo"), left, path + f"/{n}<={at}")
            if not ok:
                return ok, why
            return walk(node.get("hi"), right, path + f"/{n}>={at}")
        leaf = node.get("leaf")
        count[0] += 1
        if leaf == "interval":
            r = _reading(expr, quantities, piece)
            if r is None:
                return False, f"{path}: no interval reading"
            good = r[1] <= bound if op == "<=" else r[0] >= bound
            return (True, None) if good else (False, f"{path}: interval reading [{r[0]}, {r[1]}] does not settle {op} {bound}")
        if leaf == "monotone":
            signs = node.get("signs") or {}
            corner = {}
            for n, (lo, hi) in piece.items():
                if lo == hi:
                    corner[n] = (lo, lo)
                    continue
                s = signs.get(n)
                if s not in ("+", "-"):
                    return False, f"{path}: {n} has width and no sign"
                if n not in derivs:
                    derivs[n] = derivative(expr, n)
                r = _reading(derivs[n], quantities, piece)
                if r is None:
                    return False, f"{path}: d/d{n} has no reading on the piece"
                if s == "+" and r[0] < 0:
                    return False, f"{path}: d/d{n} in [{r[0]}, {r[1]}] is not >= 0"
                if s == "-" and r[1] > 0:
                    return False, f"{path}: d/d{n} in [{r[0]}, {r[1]}] is not <= 0"
                up = (s == "+") == (op == "<=")       # toward the extreme being bounded
                v = hi if up else lo
                corner[n] = (v, v)
            r = _reading(expr, quantities, corner)
            if r is None:
                return False, f"{path}: no value at the corner"
            good = r[1] <= bound if op == "<=" else r[0] >= bound
            return (True, None) if good else (False, f"{path}: the extreme corner gives [{r[0]}, {r[1]}], not {op} {bound}")
        return False, f"{path}: unknown leaf {leaf!r}"

    ok, why = walk(cert, box, "")
    return (True, count[0]) if ok else (False, why)
