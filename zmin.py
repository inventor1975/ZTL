# -*- coding: utf-8 -*-
"""
A LOWER BOUND ON A NONLINEAR MINIMUM, CHECKED — a split of the amounts' box, every piece settled.

WHY (2026-10-12, the universal stand's gap J3): purge fraction, surcharge height, PCM mass — continuous amounts
that enter the requirements through exp, log10, a ratio. No duality is at hand there (zlp is for the affine
case), so the authors fell back to grids and an "optimal on the grid". The claim "no mix in the box costs less
than L" is made checkable by a CERTIFICATE over the box of the amounts x:

    {"split": x, "at": "p/q", "lo": tree, "hi": tree}         the piece cut at x = at (strictly inside)
    {"leaf": "cost", "cert": c}                               the objective is >= L on this piece
                                                              (c: a zcertify tree for that bound)
    {"leaf": "fails", "row": i, "at": {d: "p/q"}, "bound": "p/q", "cert": c}
    {"leaf": "fails", "row": i, "at": {d: "p/q"}, "cert": {"leaf": "hc4"}}
                                                              the same, shown by CONTRACTION (zcontract): the
                                                              requirement met, contracted over the piece, is
                                                              EMPTY (2026-10-19)
                                                              requirement i FAILS on this piece at ONE point
                                                              of its data (d = the given point, inside the
                                                              requirement's own box): for ">= b" the row is
                                                              <= bound < b for every x of the piece, for
                                                              "<= b" it is >= bound > b, for "== b" either

SOUND: the pieces cover the box (each cut is inside its piece). A mix x lies in some leaf. On a "fails" leaf
there is a value of the data for which x misses a requirement, so x does not meet the requirements for EVERY
value of the box — it is not a robust mix. On a "cost" leaf objective(x) >= L. So every robust mix costs at
least L. All leaves "fails": no robust mix exists at all.

Each leaf's bound is checked by zcertify.check on the piece (its own readings: interval or monotone pieces),
exactly, with no budget. The search (outside) chooses the cuts, the points and L; the kernel trusts none of it.
"""

from fractions import Fraction

import zcertify as ZC


def _frac(v):
    return Fraction(str(v))


def _on(qs, piece):
    q2 = dict(qs)
    for n, (lo, hi) in piece.items():
        if n in q2:
            q2[n] = dict(q2[n], lo=lo, hi=hi)
    return q2


def check_lower_bound(objective, qs_obj, rows, xs, L, cert):
    """objective: a reader node over qs_obj (the amounts x and the objective's own data);
    rows: [(node, op, bound, qs)] — each requirement over its own box (op "<=", ">=", "==");
    xs: {x: (lo, hi)} the amounts' box; L a Fraction; cert the tree above.
    -> (True, {"pieces", "cost", "fails"}) or (False, reason)."""
    try:
        L = _frac(L)
    except (ValueError, ZeroDivisionError):
        return False, "L unreadable"
    for x, (lo, hi) in xs.items():
        if not lo <= hi:
            return False, f"{x}: empty range"
    count = {"pieces": 0, "cost": 0, "fails": 0}

    def walk(node, piece, path):
        if not isinstance(node, dict):
            return False, f"{path}: not a tree node"
        if "split" in node:
            x = node["split"]
            if x not in piece:
                return False, f"{path}: split on {x!r}, not an amount"
            try:
                at = _frac(node["at"])
            except (ValueError, ZeroDivisionError, KeyError):
                return False, f"{path}: split point unreadable"
            lo, hi = piece[x]
            if not lo < at < hi:
                return False, f"{path}: split {x} at {at} is not inside [{lo}, {hi}]"
            ok, why = walk(node.get("lo"), dict(piece, **{x: (lo, at)}), f"{path}/{x}<={at}")
            if not ok:
                return ok, why
            return walk(node.get("hi"), dict(piece, **{x: (at, hi)}), f"{path}/{x}>={at}")
        count["pieces"] += 1
        leaf = node.get("leaf")
        if leaf == "cost":
            ok, why = ZC.check(objective, _on(qs_obj, piece), ">=", L, node.get("cert"))
            if not ok:
                return False, f"{path}: objective >= {L} not shown: {why}"
            count["cost"] += 1
            return True, None
        if leaf == "fails":
            i = node.get("row")
            if not isinstance(i, int) or not 0 <= i < len(rows):
                return False, f"{path}: no requirement {i!r}"
            rnode, op, b, qs = rows[i]
            hc4 = isinstance(node.get("cert"), dict) and node["cert"].get("leaf") == "hc4"
            try:
                pt = {d: _frac(v) for d, v in (node.get("at") or {}).items()}
                bound = None if hc4 else _frac(node["bound"])
            except (ValueError, ZeroDivisionError, KeyError, AttributeError):
                return False, f"{path}: point or bound unreadable"
            for d, v in pt.items():
                if d in xs or d not in qs:
                    return False, f"{path}: {d} is not a datum of requirement {i}"
                if not qs[d]["lo"] <= v <= qs[d]["hi"]:
                    return False, f"{path}: {d} = {v} lies outside its box [{qs[d]['lo']}, {qs[d]['hi']}]"
            if hc4:
                # CONTRACTION (2026-10-19, zcontract; lean/ZContract.lean): the requirement MET is contracted over
                # the piece (the data at the point, the rest over their boxes) — an EMPTY box: no mix of the piece
                # meets it there. The kernel runs the contraction itself; the search's word is not taken.
                import zcontract as ZK
                if not ZK.empty(rnode, op, b, _on(qs, dict(piece, **{d: (v, v) for d, v in pt.items()}))):
                    return False, f"{path}: requirement {i} not contracted to empty on the piece"
                count["fails"] += 1
                return True, None
            if op == ">=" and bound < b:
                side = "<="
            elif op == "<=" and bound > b:
                side = ">="
            elif op == "==" and bound != b:
                side = "<=" if bound < b else ">="
            else:
                return False, f"{path}: bound {bound} does not miss {op} {b}"
            ok, why = ZC.check(rnode, _on(qs, dict(piece, **{d: (v, v) for d, v in pt.items()})), side, bound,
                               node.get("cert"))
            if not ok:
                return False, f"{path}: requirement {i} {side} {bound} not shown: {why}"
            count["fails"] += 1
            return True, None
        return False, f"{path}: unknown leaf {leaf!r}"

    ok, why = walk(cert, dict(xs), "")
    return (True, count) if ok else (False, why)
