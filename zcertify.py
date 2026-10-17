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
(Second tranche: E of unknowns solved from a linear system — check_system. Third,
2026-10-11: E of IMPLICIT quantities, roots of their own laws, kept moving with the
box — `check(..., implicit=)`, see IMPLICIT QUANTITIES below; Lean: lean/ZImplicit.lean (implicit_monotone_leaf).
Fourth, 2026-10-11: every reading takes min / max / ifpos one choice at a time — see CASES; Lean: lean/ZCases.lean.)

THE CERTIFICATE is a bisection tree over the box:
    {"split": name, "at": "p/q", "lo": tree, "hi": tree}   the box cut at name = at
    {"leaf": "monotone", "signs": {name: "+" | "-"}}       on this piece E is
                                                           non-decreasing (+) or
                                                           non-increasing (-) in each
                                                           listed name; its extreme
                                                           is then ONE corner
    {"leaf": "interval"}                                   E's interval reading on
                                                           the piece settles it
    {"pin": {name: "+" | "-"}, "then": tree}               (2026-10-16) each pinned
                                                           name's sign shown over the
                                                           piece as in a monotone leaf;
                                                           the tree goes on with it at
                                                           the end its sign points to
The tree covers the box by construction (each split halves a piece at a point
inside it). For a monotone leaf the kernel builds dE/dname ITSELF (symbolically),
reads it over the piece, and accepts "+" only if the reading is >= 0 (and "-" only
if <= 0); every quantity of non-zero width on the piece must carry a sign. Then E
is evaluated at the one corner the signs point to. An interval leaf is accepted
when E's interval reading on the piece is on the right side of c.

The answer is True with the number of pieces, or False with the first reason —
deterministic, never "not computed".

PROVED IN LEAN (lean/ZCertify.lean, 2026-10-10, empty axiom list): the RULE this
file walks — cuts cover their piece, an accepted tree carries its leaves' bound to
the whole box, one corner bounds a monotone piece when the value depends on the
listed quantities only — `certificate_sound`. Its PREMISES, not proved there: the
interval reading encloses the value on a piece (`iv_sound`), and a derivative read
with a sign makes the value monotone there (`deriv_sound`, the mean value theorem).
The Lean module states the rule abstractly; this code is not extracted from it —
the correspondence is by reading, and the stand test_certify.py measures it.
"""

import os
import sys
import math
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from znum import _ev, _rat_sqrt                    # noqa: E402
import zaffine as _ZA                              # noqa: E402

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


class NoDerivative(ValueError):
    """min/max have no derivative where their arguments cross; a monotone leaf cannot use them
    (an interval leaf still can)."""


def derivative(e, name):
    """dE/dname, symbolically, over the reader's nodes."""
    if isinstance(e, (int, Fraction)):
        return ZERO
    if isinstance(e, str):
        return ONE if e == name else ZERO
    op, *args = e
    # FUNCTIONS (zfunc, 2026-10-10)
    if op in ("ifpos", "ifpos_d"):            # a branch: the branch's derivative where decided, else no reading
        x, a, b = args
        da, db = derivative(a, name), derivative(b, name)
        if _is0(da) and _is0(db) and op == "ifpos" and name not in _names(x):
            return ZERO
        return ("ifpos_d", x, da, db)
    if op in ("min", "max"):
        if name in _names(e):
            raise NoDerivative(f"{op} has no derivative where its arguments cross")
        return ZERO
    if op in ("exp", "ln", "log10", "atan", "tan", "sin", "cos"):
        u = args[0]
        du = derivative(u, name)
        if _is0(du):
            return ZERO
        if op == "exp":
            return _mul(e, du)
        if op == "ln":
            return ("div", du, u)
        if op == "log10":
            return ("div", du, ("mul", u, ("ln", Fraction(10))))
        if op == "atan":
            return ("div", du, ("add", ONE, ("mul", u, u)))
        if op == "sin":
            return _mul(du, ("cos", u))
        if op == "cos":
            return _mul(du, ("sub", ZERO, ("sin", u)))
        return _mul(du, ("add", ONE, ("mul", e, e)))          # tan
    if op == "pow":
        u, v = args
        du, dv = derivative(u, name), derivative(v, name)
        if _is0(du) and _is0(dv):
            return ZERO
        if _is0(dv):                                          # v does not move with name: v·u^(v-1)·u'
            return _mul(_mul(v, ("pow", u, ("sub", v, ONE))), du)
        return _mul(e, _add(_mul(dv, ("ln", u)), ("div", _mul(v, du), u)))
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


# ── CASES: branches read one choice at a time (2026-10-11, the curator's "да"; the universal stand's blind test 5,
# c09: coverage B + F + S - N with F = min(cap, max(0, N - B)) is EXACTLY 0 wherever B < N < B + cap, and no
# enclosure with any slack proves ">= 0" there — the reading must see B + (N - B) - N cancel).
# On a piece, every min / max / ifpos whose condition the reading DECIDES is replaced by its branch; the ones it
# does not decide (at most CASE_BITS of them) are tried both ways, every combination read on its own (with the
# affine reading, so the linear parts cancel) and the HULL taken. Sound: at each point of the piece the true value
# is one combination's value there, and each combination's reading encloses its values over the whole piece.
# The result is met with the plain reading (both enclose). LEAN (2026-10-12): lean/ZCases.lean — cases_sound,
# dual_leaf_low / dual_leaf_impossible, min_enclosure / max_enclosure / meet_enclosure, zero axioms; the branch
# semantics and the readings stay named premises.
CASES = True
CASE_BITS = 6
_BRANCH = ("min", "max", "ifpos")


def _branch_nodes(e, acc):
    if isinstance(e, tuple):
        if e[0] in _BRANCH:
            acc.append(e)
        for a in e[1:]:
            if isinstance(a, list):
                for x in a:
                    _branch_nodes(x, acc)
            else:
                _branch_nodes(a, acc)
    return acc


def _unique_branches(nodes):
    """One per STRUCTURE: a subtree met twice has one value at each point, so one choice (blind test 5, c09: F
    inside S and beside it)."""
    seen, out = set(), []
    for n in nodes:
        k = repr(n)
        if k not in seen:
            seen.add(k)
            out.append(n)
    return out


def _side_of(node, qs, piece):
    """+1: the first value is taken over the whole piece (min: a <= b, max: a >= b, ifpos: x > 0); -1: the second;
    0: not decided."""
    op = node[0]
    cond = node[1] if op == "ifpos" else ("sub", node[1], node[2])
    r = _reading(cond, qs, piece, cases=False)
    if r is None:
        return 0
    if op == "ifpos":
        return 1 if r[0] > 0 else (-1 if r[1] <= 0 else 0)
    if op == "min":
        return 1 if r[1] <= 0 else (-1 if r[0] >= 0 else 0)
    return 1 if r[0] >= 0 else (-1 if r[1] <= 0 else 0)          # max


def _resolve(e, sides):
    if isinstance(e, tuple):
        if e[0] in _BRANCH and repr(e) in sides:
            first = e[2] if e[0] == "ifpos" else e[1]
            second = e[3] if e[0] == "ifpos" else e[2]
            return _resolve(first if sides[repr(e)] == 1 else second, sides)
        return (e[0], *[[_resolve(x, sides) for x in a] if isinstance(a, list) else _resolve(a, sides) for a in e[1:]])
    return e


def _dual_low(f, gs):
    """A lower bound of the affine f over the inputs' cube [-1, 1]^n where every affine g in gs is <= 0 (each g's
    own error allowed for) — weak duality: for ANY lam >= 0, min over the cube of f + sum lam_j (g_j - err_j),
    minus f's error. lam is sought coordinate by coordinate among the breakpoints (any lam is sound; a good one is
    tight). Returns (bound, impossible): impossible when some lam proves the constraints cannot hold together."""
    keys = set(f.t)
    for g in gs:
        keys |= set(g.t)
    keys = sorted(keys, key=repr)

    def value(lam, with_f):
        c = (f.c - f.e) if with_f else Fraction(0)
        t = {k: (f.t.get(k, Fraction(0)) if with_f else Fraction(0)) for k in keys}
        for l, g in zip(lam, gs):
            if l:
                c += l * (g.c - g.e)
                for k in keys:
                    t[k] += l * g.t.get(k, Fraction(0))
        return c - sum((abs(v) for v in t.values()), Fraction(0))

    def ascend(with_f):
        lam = [Fraction(0)] * len(gs)
        best = value(lam, with_f)
        for _ in range(3):
            for j, g in enumerate(gs):
                cands = {Fraction(0)}
                for k in keys:
                    b = g.t.get(k, Fraction(0))
                    if b:
                        a = (f.t.get(k, Fraction(0)) if with_f else Fraction(0)) + \
                            sum((l * h.t.get(k, Fraction(0)) for i, (l, h) in enumerate(zip(lam, gs)) if i != j),
                                Fraction(0))
                        x = -a / b
                        if x > 0:
                            cands.add(x)
                if not with_f:
                    cands |= {x * 2 for x in list(cands)} | {Fraction(1)}
                for x in cands:
                    trial = lam[:j] + [x] + lam[j + 1:]
                    v = value(trial, with_f)
                    if v > best:
                        best, lam = v, trial
        return best
    if gs and ascend(False) > 0:
        return None, True
    return ascend(True), False


CASE_LEAVES = 256      # combinations read on one piece at most; more and the piece is read plainly (a cut follows)


class _TooMany(Exception):
    pass


def _cond_g(n, side):
    """The condition under which `side` of branch n is taken, as g <= 0 (closed)."""
    if n[0] == "ifpos":
        return ("sub", 0, n[1]) if side == 1 else n[1]                 # x > 0  /  x <= 0
    if n[0] == "min":
        return ("sub", n[1], n[2]) if side == 1 else ("sub", n[2], n[1])
    return ("sub", n[2], n[1]) if side == 1 else ("sub", n[1], n[2])   # max


def _case_reading(e, qs, piece, base):
    # an OUTER min / max: its bound is the min / max of its arguments' bounds — each read by cases on its own
    if isinstance(e, tuple) and e[0] in ("min", "max"):
        ra = _reading(e[1], qs, piece)
        rb = _reading(e[2], qs, piece)
        if ra is None or rb is None:
            return base
        r = (min(ra[0], rb[0]), min(ra[1], rb[1])) if e[0] == "min" else (max(ra[0], rb[0]), max(ra[1], rb[1]))
        if base is None:
            return r
        lo, hi = max(r[0], base[0]), min(r[1], base[1])
        return (lo, hi) if lo <= hi else base
    if not _branch_nodes(e, []):
        return base
    q2 = dict(qs)
    for n_, (a_, b_) in piece.items():
        q2[n_] = dict(qs[n_], lo=a_, hi=b_)
    leaves = []

    def settle(f, gs):
        """Every branch the reading decides on the piece, replaced — until none is left to decide."""
        while True:
            sides = {}
            for n in _unique_branches(_branch_nodes(f, [])):
                sd = _side_of(n, qs, piece)
                if sd:
                    sides[repr(n)] = sd
            if not sides:
                return f, gs
            f = _resolve(f, sides)
            gs = [_resolve(g, sides) for g in gs]

    def go(f, gs):
        # A TREE, not the product (2026-10-11, c09's cost: 7 undecided of 20 — most decide themselves once a
        # neighbour is chosen, max(0, N - B - F) with F = N - B is max(0, 0)): choose one undecided branch, both
        # ways, settle what that decides, go on; each choice's condition is kept as g <= 0
        f, gs = settle(f, gs)
        open_ = _unique_branches(_branch_nodes(f, []))
        if not open_:
            leaves.append((f, gs))
            if len(leaves) > CASE_LEAVES:
                raise _TooMany()
            return
        n = min(open_, key=lambda x: len(repr(x)))          # an innermost one first
        for side in (1, -1):
            sub = {repr(n): side}
            go(_resolve(f, sub), [_resolve(g, sub) for g in gs] + [_resolve(_cond_g(n, side), sub)])
    try:
        go(e, [])
    except _TooMany:
        return base
    lo = hi = None
    for fe, gs in leaves:
        r = _reading(fe, qs, piece, cases=False, affine=True)
        if r is None:
            return base
        affs = _ZA.read([fe, ("sub", 0, fe)] + gs, qs, piece, _rat_sqrt, lambda n_: _plain(n_, q2), shared=True)
        if affs:
            low, impossible = _dual_low(affs[0], affs[2:])
            if impossible:
                continue                    # no point of the piece is in this case
            neg, _ = _dual_low(affs[1], affs[2:])
            r = (max(r[0], low), min(r[1], -neg))
            if r[0] > r[1]:
                continue
        lo = r[0] if lo is None else min(lo, r[0])
        hi = r[1] if hi is None else max(hi, r[1])
    if lo is None:
        return base
    if base is None:
        return lo, hi
    lo, hi = max(lo, base[0]), min(hi, base[1])
    return (lo, hi) if lo <= hi else base


def _reading(e, qs, piece, cases=None, affine=None):
    """E's interval over the piece (each name's box replaced), or None."""
    base = _reading_one(e, qs, piece, AFFINE if affine is None else affine)
    if (CASES if cases is None else cases):
        return _case_reading(e, qs, piece, base)
    return base


def _reading_one(e, qs, piece, affine):
    q2 = dict(qs)
    for n, (lo, hi) in piece.items():
        q2[n] = dict(qs[n], lo=lo, hi=hi)
    import znum as _ZN
    keep, _ZN._MEMO[0] = _ZN._MEMO[0], {}       # one reading: each distinct node once (znum._ev, a graph's memory)
    try:
        iv = _ev(e, q2)[0]
    except (ZeroDivisionError, KeyError, ValueError, ArithmeticError):
        return None
    finally:
        _ZN._MEMO[0] = keep
    if iv is None:
        return None
    lo, hi = iv
    if isinstance(lo, float) or isinstance(hi, float):
        return None           # an infinite end: nothing certified from it
    # AFFINE reading (zaffine.py, 2026-10-10): remembers which input a spread came from; intersected with
    # the plain one — both enclose, the meet is never wider. Not applied to a POINT reading (nothing to gain).
    if affine and any(qs[n]["lo"] != qs[n]["hi"] if n not in piece else piece[n][0] != piece[n][1]
                      for n in _names(e) if n in qs):
        af = _ZA.read(e, qs, piece, _rat_sqrt, lambda n: _plain(n, q2))
        if af is not None and af[0] <= hi and af[1] >= lo:
            lo, hi = max(lo, af[0]), min(hi, af[1])
    return lo, hi


AFFINE = True


def _plain(e, q2):
    try:
        iv = _ev(e, q2)[0]
    except (ZeroDivisionError, KeyError, ValueError, ArithmeticError):
        return None
    return iv


def check(expr, quantities, op, bound, cert, implicit=None):
    """Is `expr op bound` true over the quantities' whole box, by this certificate?
    `expr` a reader node (znumjudge._parse_arith), `op` "<=" or ">=", `bound` a
    Fraction. Returns (True, pieces) or (False, reason).

    implicit = {U: g}: U in expr is not a boxed quantity but a ROOT of g(U, x) = 0 (g a reader node of
    U and the boxed quantities only), sought in U's own range in `quantities` — see IMPLICIT below."""
    if op not in ("<=", ">="):
        return False, f"op {op!r}: only <= and >= are certified"
    implicit = implicit or {}
    for u, g in implicit.items():
        if u not in quantities:
            return False, f"implicit {u}: no range given"
        extra = _names(g) & set(implicit) - {u}
        if extra:
            return False, f"implicit {u}: its law uses the implicit {sorted(extra)} (coupled roots: not read)"
    used = set(_names(expr))
    for g in implicit.values():
        used |= _names(g)
    names = sorted(n for n in used if n in quantities and n not in implicit)
    box = {n: (quantities[n]["lo"], quantities[n]["hi"]) for n in names}
    for n, (lo, hi) in list(box.items()) + [(u, (quantities[u]["lo"], quantities[u]["hi"])) for u in implicit]:
        if isinstance(lo, float) or isinstance(hi, float):
            return False, f"{n} is unbounded: no certificate covers an infinite box"
    derivs = {}
    count = [0]
    roots_of = _implicit_roots(implicit, quantities)

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
        if "pin" in node:
            # PIN (2026-10-16, the curator's "б"; zlin's pin for the nonlinear certificate): each named quantity's
            # derivative has its sign over the WHOLE piece (read as in a monotone leaf, the implicit roots in their
            # brackets) -> the extreme of the piece lies with it at the end its sign points to; the rest of the tree
            # is checked on that smaller piece. Signs read on the piece hold on every part of it, so several pin
            # together. (A 28-datum rocket motor: 16 of 18 signs at once, the other two then in 2 dimensions.)
            pins = node.get("pin")
            if not isinstance(pins, dict) or not pins:
                return False, f"{path}: a pin names no quantity"
            count[0] += 1
            rpiece = piece
            if implicit:
                ok, at_piece = roots_of(node.get("roots"), piece)
                if not ok:
                    return False, f"{path}: {at_piece}"
                if not all(u in (node.get("roots") or {}) for u in implicit):
                    return False, f"{path}: a pin with an implicit quantity needs its bracket on the piece"
                rpiece = dict(piece, **at_piece)
            child = dict(piece)
            gg = _graph_grad(expr, quantities, rpiece, [n for n in pins if n in piece and n not in implicit],
                             implicit) if not any(n not in piece or n in implicit for n in pins) else {}
            for n, s in pins.items():
                if n not in piece or n in implicit:
                    return False, f"{path}: pin on {n!r}, not a quantity of the expression"
                lo, hi = piece[n]
                if lo == hi:
                    return False, f"{path}: pin on {n}, already a point"
                if s not in ("+", "-"):
                    return False, f"{path}: pin {n} with no sign"
                r = gg.get(n)
                if r is None or not (s == "+" and r[0] >= 0 or s == "-" and r[1] <= 0):
                    if n not in derivs:
                        try:
                            derivs[n] = _total_derivative(expr, n, implicit)
                        except NoDerivative as why:
                            return False, f"{path}: {why} — no pin on it"
                    r = _reading(derivs[n], quantities, rpiece)
                if r is None:
                    return False, f"{path}: d/d{n} has no reading on the piece"
                if s == "+" and r[0] < 0 or s == "-" and r[1] > 0:
                    return False, f"{path}: d/d{n} in [{r[0]}, {r[1]}] has not the sign {s} the pin says"
                up = (s == "+") == (op == "<=")
                v = hi if up else lo
                child[n] = (v, v)
            return walk(node.get("then"), child, path + "/pin(" + ",".join(sorted(pins)) + ")")
        leaf = node.get("leaf")
        count[0] += 1
        if implicit:
            ok, at_piece = roots_of(node.get("roots"), piece)
            if not ok:
                return False, f"{path}: {at_piece}"
            piece = dict(piece, **at_piece)          # each U read over its bracket on this piece
        if leaf == "interval":
            r = _reading(expr, quantities, piece)
            if r is None:
                return False, f"{path}: no interval reading"
            good = r[1] <= bound if op == "<=" else r[0] >= bound
            return (True, None) if good else (False, f"{path}: interval reading [{r[0]}, {r[1]}] does not settle {op} {bound}")
        if leaf == "monotone":
            signs = node.get("signs") or {}
            if implicit and not all(u in (node.get("roots") or {}) for u in implicit):
                return False, f"{path}: a monotone leaf with an implicit quantity needs its bracket on the piece"
            corner = {}
            gg = _graph_grad(expr, quantities, piece,
                             [n for n, (lo, hi) in piece.items() if n not in implicit and lo != hi], implicit)
            for n, (lo, hi) in piece.items():
                if n in implicit:
                    continue
                if lo == hi:
                    corner[n] = (lo, lo)
                    continue
                s = signs.get(n)
                if s not in ("+", "-"):
                    return False, f"{path}: {n} has width and no sign"
                r = gg.get(n)
                if r is None or not (s == "+" and r[0] >= 0 or s == "-" and r[1] <= 0):
                    if n not in derivs:
                        try:
                            derivs[n] = _total_derivative(expr, n, implicit)
                        except NoDerivative as why:
                            return False, f"{path}: {why} — a monotone leaf cannot use it (an interval leaf can)"
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
            if implicit:
                ok, at_corner = roots_of(node.get("corner_roots"), corner)
                if not ok:
                    return False, f"{path}: at the corner: {at_corner}"
                corner = dict(corner, **at_corner)
            r = _reading(expr, quantities, corner)
            if r is None:
                return False, f"{path}: no value at the corner"
            good = r[1] <= bound if op == "<=" else r[0] >= bound
            return (True, None) if good else (False, f"{path}: the extreme corner gives [{r[0]}, {r[1]}], not {op} {bound}")
        return False, f"{path}: unknown leaf {leaf!r}"

    ok, why = walk(cert, box, "")
    return (True, count[0]) if ok else (False, why)


# ── IMPLICIT QUANTITIES (third tranche, 2026-10-11, the universal stand's gap J6) ──────────
# The bound is on E(x, U) where U is a root of g(U, x) = 0 — a pump's operating point, a cell's
# current through its own polarisation. Given U as a free box the reading forgets that U moves WITH x
# (c02 of blind test 4: Es = Ea - I*R read with Ea and I independent, 0.036 V too wide where the
# margin was 0.002 V). Here U stays a function of x:
#   UNIQUE: dg/dU has one strict sign over the piece × U's whole range -> at most one root there for
#           each x (U's range itself — that no root lies outside it — is zimplicit's certificate, checked
#           apart; this file never widens it);
#   BRACKET "roots": {U: [a, b]} on a leaf, inside U's range: g(a, piece) and g(b, piece) read on the
#           two sides of 0 the sign of dg/dU asks for -> for EVERY x of the piece the root exists and
#           lies in [a, b] (intermediate values). Without a bracket an interval leaf reads U over its
#           whole range (nothing claimed about it);
#   MONOTONE: on a piece where the root is unique and bracketed, U(x) is continuous (one root of a
#           closed graph in a compact bracket) and, as dg/dU != 0, differentiable with
#           dU/dx = -g_x / g_U (the implicit function theorem); E's TOTAL derivative
#           dE/dx + dE/dU * dU/dx is read over the piece × the bracket. A sign makes E(x, U(x))
#           monotone in x on the piece (mean value theorem), and the corner the signs point to is
#           read with U in the bracket "corner_roots" checked AT that corner.
# LEAN (2026-10-12): lean/ZImplicit.lean — root_unique, root_in_bracket, implicit_monotone_leaf (zero axioms): the
# kernel's combination is proved; the implicit function and mean value theorems (the total derivative's sign makes
# E(x, U(x)) monotone) and the intermediate value theorem (a sign change gives a root) stay named premises.
def _implicit_roots(implicit, quantities):
    usign = {}

    def at(brackets, piece):
        """(True, {U: (a, b)}) — each U's bracket over the piece, checked — or (False, why)."""
        out = {}
        brackets = brackets or {}
        for u, g in implicit.items():
            rlo, rhi = quantities[u]["lo"], quantities[u]["hi"]
            if u not in brackets:
                out[u] = (rlo, rhi)              # anywhere in its range: claims nothing
                continue
            try:
                a, b = (Fraction(str(x)) for x in brackets[u])
            except (ValueError, TypeError, ZeroDivisionError):
                return False, f"the bracket of {u} is unreadable"
            if not (rlo <= a <= b <= rhi):
                return False, f"the bracket [{a}, {b}] of {u} leaves its range [{rlo}, {rhi}]"
            key = (u, tuple(sorted(piece.items())))
            if key not in usign:
                try:
                    r = _reading(derivative(g, u), quantities, dict(piece, **{u: (rlo, rhi)}))
                except NoDerivative as why:
                    return False, f"d{u} of its law: {why}"
                usign[key] = None if r is None else (1 if r[0] > 0 else -1 if r[1] < 0 else None)
            s = usign[key]
            if s is None:
                return False, f"d/d{u} of its law does not keep one strict sign over the piece × [{rlo}, {rhi}]"
            ra = _reading(g, quantities, dict(piece, **{u: (a, a)}))
            rb = _reading(g, quantities, dict(piece, **{u: (b, b)}))
            if ra is None or rb is None:
                return False, f"the law of {u} has no reading at its bracket"
            if not ((ra[1] <= 0 <= rb[0]) if s > 0 else (ra[0] >= 0 >= rb[1])):
                return False, f"the law of {u} does not change sign across [{a}, {b}] on the piece"
            out[u] = (a, b)
        return True, out
    return at


def _total_derivative(expr, n, implicit):
    """dE/dn with every implicit U a function of the boxed quantities: + dE/dU * (-g_n / g_U)."""
    d = derivative(expr, n)
    for u, g in (implicit or {}).items():
        du_e = derivative(expr, u)
        gn = derivative(g, n)
        if _is0(du_e) or _is0(gn):
            continue
        d = _add(d, _mul(du_e, ("div", ("sub", ZERO, gn), derivative(g, u))))
    return d


# ── DERIVATIVES ALONG THE GRAPH (2026-10-16, the curator's "да, делай шаг 2") ─────────────────────────────────
# The symbolic dE/dn of a long expression (a rocket's delta-v: 9 000 characters, the chamber pressure in it five
# times) is a still longer tree, read once per quantity. Here E is walked ONCE as a graph (a repeated subtree is one
# node): each node's value is the kernel's own reading (_ev, with the node memory), its derivatives by the chain rule
# with interval arithmetic on exact fractions, every result rounded OUTWARD to 2^-62 of its size. An implicit root U
# enters with dU/dp = -g_p/g_U (g's own graph derivatives over U's bracket; g_U must keep one sign). Branches (ifpos,
# min, max) give no derivative here — the symbolic reading stays. Both are enclosures: a sign is accepted when
# EITHER shows it (monotone leaf and pin), so nothing the kernel accepted before is lost.
def _iv_out(iv):
    lo, hi = iv
    m = max(abs(lo), abs(hi))
    if m == 0:
        return iv
    k = m.numerator.bit_length() - m.denominator.bit_length() - 62
    st = Fraction(2) ** k
    return (Fraction(math.floor(lo / st)) * st, Fraction(math.ceil(hi / st)) * st)


def _iadd(a, b):
    return _iv_out((a[0] + b[0], a[1] + b[1]))


def _ineg(a):
    return (-a[1], -a[0])


def _imul2(a, b):
    ps = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return _iv_out((min(ps), max(ps)))


def _idiv2(a, b):
    if b[0] <= 0 <= b[1]:
        return None
    return _imul2(a, (1 / b[1], 1 / b[0]) if b[0] > 0 else (1 / b[1], 1 / b[0]))


def _graph_grad(expr, quantities, piece, wrt, implicit=None):
    """{name: (lo, hi) | None} — dE/dname enclosed over the piece (implicit roots in their brackets, in `piece`)."""
    import znum as _ZN
    wrt = set(wrt)
    q2 = dict(quantities)
    for n, (lo, hi) in piece.items():
        q2[n] = dict(quantities[n], lo=lo, hi=hi)
    keep = _ZN._MEMO[0]
    _ZN._MEMO[0] = {}
    UNK = object()

    def val(node):
        iv = _ev(node, q2)[0]
        if iv is None or isinstance(iv[0], float) or isinstance(iv[1], float):
            raise ArithmeticError("no reading")
        return iv
    try:
        memo = {}
        roots = {}

        def grad(node):
            key = node if not isinstance(node, tuple) or node[0] != "sum" else None
            if key is not None and key in memo:
                return memo[key]
            g = _grad(node)
            if key is not None:
                memo[key] = g
            return g

        def comb(*parts):
            """sum over (gradient dict, factor interval) — UNK for a name any part cannot read."""
            out = {}
            for gd, f in parts:
                for k, v in gd.items():
                    t = UNK if v is UNK or f is None else _imul2(v, f)
                    if k in out:
                        out[k] = UNK if out[k] is UNK or t is UNK else _iadd(out[k], t)
                    else:
                        out[k] = t
            return out

        def _grad(node):
            if isinstance(node, Fraction) or isinstance(node, (int, float)):
                return {}
            if isinstance(node, str):
                if node in roots:
                    return roots[node]
                return {node: (Fraction(1), Fraction(1))} if node in wrt else {}
            op, *args = node
            if not (_names(node) & (wrt | set(roots))):
                return {}
            one = (Fraction(1), Fraction(1))
            if op == "sum":
                return comb(*[(grad(a), one) for a in args[0]])
            if op in ("add", "sub"):
                gb = grad(args[1])
                return comb((grad(args[0]), one), (gb, one if op == "add" else (Fraction(-1), Fraction(-1))))
            if op == "mul":
                return comb((grad(args[0]), val(args[1])), (grad(args[1]), val(args[0])))
            if op == "div":
                b = val(args[1])
                if b[0] <= 0 <= b[1]:
                    raise ArithmeticError("a divisor across zero")
                inv = _idiv2(one, b)
                v = val(node)
                return comb((grad(args[0]), inv), (grad(args[1]), _ineg(_imul2(v, inv))))
            if op == "pow":
                a, c = args
                gc = grad(c)
                if not gc:
                    cv = val(c)
                    if cv[0] != cv[1]:
                        raise ArithmeticError("an exponent with width but no names")
                    f = _imul2(cv, val(("pow", a, cv[0] - 1)))
                    return comb((grad(a), f))
                v = val(node)
                a_v = val(a)
                if a_v[0] <= 0:
                    raise ArithmeticError("a variable exponent of a base not positive")
                return comb((grad(a), _imul2(v, _idiv2(val(c), a_v))), (gc, _imul2(v, val(("ln", a)))))
            if op == "exp":
                return comb((grad(args[0]), val(node)))
            if op == "ln":
                return comb((grad(args[0]), _idiv2(one, val(args[0]))))
            if op == "log10":
                return comb((grad(args[0]), _idiv2(one, _imul2(val(args[0]), val(("ln", Fraction(10)))))))
            if op == "sqrt":
                v = val(node)
                return comb((grad(args[0]), _idiv2(one, _imul2((Fraction(2), Fraction(2)), v))))
            if op == "sin":
                return comb((grad(args[0]), val(("cos", args[0]))))
            if op == "cos":
                return comb((grad(args[0]), _ineg(val(("sin", args[0])))))
            if op == "atan":
                a = val(args[0])
                return comb((grad(args[0]), _idiv2(one, _iadd(one, _imul2(a, a)))))
            if op == "tan":
                v = val(node)
                return comb((grad(args[0]), _iadd(one, _imul2(v, v))))
            return {k: UNK for k in _names(node) & (wrt | set(roots))}      # a branch: no derivative here

        for u, g in (implicit or {}).items():
            # g's derivatives in U and in each quantity, over U's bracket (in the piece)
            wrt_u = wrt | {u}
            saved = wrt
            wrt = wrt_u
            memo.clear()
            gg = grad(g)
            wrt = saved
            memo.clear()
            gu = gg.get(u)
            if gu is None or gu is UNK or gu[0] <= 0 <= gu[1]:
                roots[u] = {k: UNK for k in wrt}
                continue
            inv = _idiv2((Fraction(-1), Fraction(-1)), gu)
            roots[u] = {k: (UNK if v is UNK else _imul2(v, inv)) for k, v in gg.items() if k != u}
        out = grad(expr)
        return {n: (None if out.get(n, (Fraction(0), Fraction(0))) is UNK else out.get(n, (Fraction(0), Fraction(0))))
                for n in wrt}
    except (ArithmeticError, ZeroDivisionError, KeyError, ValueError, TypeError):
        return {n: None for n in wrt}
    finally:
        _ZN._MEMO[0] = keep


# ── TAYLOR COEFFICIENTS ALONG THE GRAPH (2026-10-16, the curator's "делай Тейлора по графу") ─────────────────────
# c_k = f^(k)(x)/k! for x in an interval X, k = 0..n, by the classic recurrences over the graph (each shared node
# once): sums termwise, products by convolution, quotients, exp, ln, sqrt, pow (a constant exponent; a variable one as
# exp(c ln a)), sin/cos together, atan, log10. Each node's c_0 is the kernel's own reading over X (and the box); the
# rest is interval arithmetic on fractions rounded outward. With X a point: the coefficients there; with X a piece:
# for every xi in it c_k(xi) lies in the result — so f^(n)(xi)/n! over a piece, the Lagrange remainder's factor.
# Branches (ifpos, min, max): None — the symbolic derivatives stay (zintegral falls back to them).
def _sub2(a, b):
    return _iv_out((a[0] - b[1], a[1] - b[0]))


def _scal(a, c):
    return _imul2(a, (Fraction(c), Fraction(c)))


def taylor_coeffs(expr, x, quantities, piece, n, trace=None):
    """[(lo, hi)] * (n + 1): f^(k)/k! over piece[x] (and the box of the other names), or None.
    trace: a dict to receive every node's series (sums excepted) — ztaylorcert checks them against the Lean reading."""
    import znum as _ZN
    q2 = dict(quantities)
    for nm, (lo, hi) in piece.items():
        q2[nm] = dict(quantities[nm], lo=lo, hi=hi)
    X = piece[x]
    keep = _ZN._MEMO[0]
    _ZN._MEMO[0] = {}
    Z = (Fraction(0), Fraction(0))

    def val(node):
        iv = _ev(node, q2)[0]
        if iv is None or isinstance(iv[0], float) or isinstance(iv[1], float):
            raise ArithmeticError("no reading")
        return iv
    try:
        memo = {}

        def tc(node):
            if not isinstance(node, tuple) or node[0] != "sum":
                if node in memo:
                    return memo[node]
            r = _tc(node)
            if not isinstance(node, tuple) or node[0] != "sum":
                memo[node] = r
            return r

        def const(iv):
            return [iv] + [Z] * n

        def mul(a, b):
            return [_iv_sum([_imul2(a[i], b[k - i]) for i in range(k + 1)]) for k in range(n + 1)]

        def _tc(node):
            if isinstance(node, (Fraction, int)):
                v = Fraction(node)
                return const((v, v))
            if isinstance(node, str):
                if node == x:
                    return [X, (Fraction(1), Fraction(1))] + [Z] * (n - 1)
                return const(val(node))
            op, *args = node
            if x not in _names(node):
                return const(val(node))
            if op == "sum":
                parts = [tc(a) for a in args[0]]
                return [_iv_sum([p[k] for p in parts]) for k in range(n + 1)]
            if op in ("add", "sub"):
                a, b = tc(args[0]), tc(args[1])
                return [(_iadd(a[k], b[k]) if op == "add" else _sub2(a[k], b[k])) for k in range(n + 1)]
            if op == "mul":
                return mul(tc(args[0]), tc(args[1]))
            if op == "div":
                a, b = tc(args[0]), tc(args[1])
                b0 = b[0]
                if b0[0] <= 0 <= b0[1]:
                    raise ArithmeticError("a divisor across zero")
                q = [val(node)]
                for k in range(1, n + 1):
                    acc = a[k]
                    for i in range(1, k + 1):
                        acc = _sub2(acc, _imul2(b[i], q[k - i]))
                    q.append(_idiv2(acc, b0))
                return q
            if op == "exp":
                a = tc(args[0])
                e = [val(node)]
                for k in range(1, n + 1):
                    e.append(_scal(_iv_sum([_scal(_imul2(a[i], e[k - i]), i) for i in range(1, k + 1)]), Fraction(1, k)))
                return e
            if op in ("ln", "log10"):
                a = tc(args[0])
                a0 = a[0]
                if a0[0] <= 0:
                    raise ArithmeticError("ln of a range not positive")
                l = [val(("ln", args[0]))]
                for k in range(1, n + 1):
                    acc = a[k]
                    if k > 1:
                        acc = _sub2(acc, _scal(_iv_sum([_scal(_imul2(l[i], a[k - i]), i) for i in range(1, k)]), Fraction(1, k)))
                    l.append(_idiv2(acc, a0))
                if op == "log10":
                    ln10 = val(("ln", Fraction(10)))
                    return [val(node)] + [_idiv2(l[k], ln10) for k in range(1, n + 1)]
                return l
            if op == "sqrt":
                a = tc(args[0])
                s0 = val(node)
                if s0[0] <= 0:
                    raise ArithmeticError("sqrt at or near 0: its derivatives are unbounded")
                sq = [s0]
                two_s0 = _scal(s0, 2)
                for k in range(1, n + 1):
                    acc = a[k]
                    if k > 1:
                        acc = _sub2(acc, _iv_sum([_imul2(sq[i], sq[k - i]) for i in range(1, k)]))
                    sq.append(_idiv2(acc, two_s0))
                return sq
            if op == "pow":
                base, c = args
                if x in _names(c):
                    return tc(("exp", ("mul", c, ("ln", base))))
                cv = val(c)
                if cv[0] != cv[1]:
                    # an exponent with a box: as exp(c ln a), c a constant series
                    return tc(("exp", ("mul", c, ("ln", base))))
                cc = cv[0]
                a = tc(base)
                a0 = a[0]
                if a0[0] <= 0 <= a0[1]:
                    raise ArithmeticError("a power of a range across 0")
                p = [val(node)]
                for k in range(1, n + 1):
                    acc = _iv_sum([_scal(_imul2(a[k - i], p[i]), cc * (k - i) - i) for i in range(k)])
                    p.append(_idiv2(acc, _scal(a0, k)))
                return p
            if op in ("sin", "cos"):
                a = tc(args[0])
                sn = [val(("sin", args[0]))]
                cs = [val(("cos", args[0]))]
                for k in range(1, n + 1):
                    sn.append(_scal(_iv_sum([_scal(_imul2(a[i], cs[k - i]), i) for i in range(1, k + 1)]), Fraction(1, k)))
                    cs.append(_scal(_iv_sum([_scal(_imul2(a[i], sn[k - i]), i) for i in range(1, k + 1)]), Fraction(-1, k)))
                memo[("cos" if op == "sin" else "sin", args[0])] = cs if op == "sin" else sn
                return sn if op == "sin" else cs
            if op == "atan":
                a = tc(args[0])
                u = mul(a, a)
                u[0] = _iadd(u[0], (Fraction(1), Fraction(1)))
                da = [_scal(a[k + 1], k + 1) for k in range(n)] + [Z]       # a' as a series (one order lost at n)
                # w = a' / u
                w = []
                for k in range(n + 1):
                    acc = da[k]
                    for i in range(1, k + 1):
                        acc = _sub2(acc, _imul2(u[i], w[k - i]))
                    w.append(_idiv2(acc, u[0]))
                return [val(node)] + [_scal(w[k - 1], Fraction(1, k)) for k in range(1, n + 1)]
            if op == "tan":
                return tc(("div", ("sin", args[0]), ("cos", args[0])))
            raise ArithmeticError(f"no series for {op}")
        out = tc(expr)
        if trace is not None:
            trace.update(memo)
        return out
    except (ArithmeticError, ZeroDivisionError, KeyError, ValueError, TypeError, _ZN._NoReadings):
        return None
    finally:
        _ZN._MEMO[0] = keep


def _iv_sum(ivs):
    lo = hi = Fraction(0)
    for a in ivs:
        lo, hi = lo + a[0], hi + a[1]
    return _iv_out((lo, hi))


# ── A QUANTITY SOLVED FROM A SYSTEM (second tranche, 2026-10-09) ──────────────
# The bound is on an expression of UNKNOWNS fixed by linear equalities whose
# coefficients are expressions of boxed quantities: P = VL*I with V - VL == I*Rs,
# VL == I*RL. A free box per unknown would lose their correlation with the
# tolerances; so the kernel solves the system ITSELF — Cramer's rule, the
# determinants kept as cofactor trees of the reader's nodes (no expansion) — and
# checks the certificate on the solved expression. Nothing the caller says about
# the solution is used. The determinant is never certified apart: every leaf reads
# the expression, which divides by it, and a reading over a piece where the
# determinant's range touches zero has no value — the leaf is refused. So an
# accepted certificate also shows the system uniquely solvable on the whole box.
# Above MAX_SYSTEM unknowns (n! cofactor terms) the kernel refuses aloud — the same
# answer every time, not a budget that runs out.
MAX_SYSTEM = 6


class SystemError_(ValueError):
    pass


def _lin(node, unknowns):
    """node -> {unknown or 1: coefficient node}, linear in the unknowns."""
    if isinstance(node, (int, Fraction)):
        return {1: Fraction(node)}
    if isinstance(node, str):
        return {node: ONE} if node in unknowns else {1: node}
    op, *args = node
    if op == "sum":
        out = {}
        for a in args[0]:
            for k, v in _lin(a, unknowns).items():
                out[k] = _add(out[k], v) if k in out else v
        return out
    if op == "sqrt" or op in ("exp", "ln", "log10", "atan", "tan", "sin", "cos", "pow", "min", "max"):
        if _names(node) & unknowns:
            raise SystemError_(f"an unknown inside {op}(...): not a linear system")
        return {1: node}
    a, b = _lin(args[0], unknowns), _lin(args[1], unknowns)
    if op in ("add", "sub"):
        out = dict(a)
        for k, v in b.items():
            if op == "add":
                out[k] = _add(out[k], v) if k in out else v
            else:
                out[k] = ("sub", out[k], v) if k in out else ("sub", ZERO, v)
        return out
    if op == "mul":
        if set(a) <= {1}:
            return {k: _mul(a.get(1, ZERO), v) for k, v in b.items()}
        if set(b) <= {1}:
            return {k: _mul(v, b.get(1, ZERO)) for k, v in a.items()}
        raise SystemError_("a product of two unknowns: not a linear system")
    if op == "div":
        if set(b) <= {1}:
            return {k: ("div", v, b.get(1, ZERO)) for k, v in a.items()}
        raise SystemError_("a division by an unknown: not a linear system")
    raise SystemError_(f"cannot read {op!r}")


def _det(M):
    n = len(M)
    if n == 1:
        return M[0][0]
    out = ZERO
    for j in range(n):
        if _is0(M[0][j]):
            continue
        term = _mul(M[0][j], _det([row[:j] + row[j + 1:] for row in M[1:]]))
        out = _add(out, term) if j % 2 == 0 else ("sub", out, term)
    return out


def solve_system(laws, unknowns, quantities):
    """{unknown: node} by Cramer's rule. laws: "lhs == rhs" strings."""
    from znumjudge import _parse_arith
    unknowns = sorted(set(unknowns))
    n = len(unknowns)
    if n > MAX_SYSTEM:
        raise SystemError_(f"{n} unknowns: more than {MAX_SYSTEM} (n! cofactor terms) — refused, not computed")
    rows = []
    for law in laws:
        if law.count("==") != 1:
            raise SystemError_(f"not one equality: {law!r}")
        l, r = law.split("==")
        a = _lin(_parse_arith(l, quantities), set(unknowns))
        b = _lin(_parse_arith(r, quantities), set(unknowns))
        row = dict(a)
        for k, v in b.items():
            row[k] = ("sub", row[k], v) if k in row else ("sub", ZERO, v)
        rows.append(row)
    if len(rows) != n:
        raise SystemError_(f"{len(rows)} equalities for {n} unknowns: not a square system")
    A = [[row.get(u, ZERO) for u in unknowns] for row in rows]
    rhs = [("sub", ZERO, row[1]) if 1 in row else ZERO for row in rows]
    D = _det(A)
    if _is0(D):
        raise SystemError_("the determinant is identically zero")
    return {u: ("div", _det([r[:i] + [rhs[k]] + r[i + 1:] for k, r in enumerate(A)]), D)
            for i, u in enumerate(unknowns)}


def _subst(node, sol):
    if isinstance(node, str):
        return sol.get(node, node)
    if isinstance(node, tuple):
        op, *args = node
        return (op, *[[_subst(x, sol) for x in a] if isinstance(a, list) else _subst(a, sol) for a in args])
    return node


def check_system(target, laws, unknowns, quantities, op, bound, cert):
    """Is `target op bound` over the box, where the target is an expression (text) of
    boxed quantities AND unknowns fixed by the linear `laws`? The kernel solves the
    system itself, then `check`. (True, pieces) or (False, reason)."""
    from znumjudge import _parse_arith
    try:
        sol = solve_system(laws, unknowns, quantities)
        e = _subst(_parse_arith(target, quantities), sol)
    except (SystemError_, ValueError) as err:
        return False, f"system: {err}"
    if _names(e) & set(unknowns):
        return False, "system: an unknown is left in the target"
    return check(e, quantities, op, bound, cert)
