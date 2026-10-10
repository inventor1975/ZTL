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
    if op in ("exp", "ln", "log10", "atan", "tan"):
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
    # AFFINE reading (zaffine.py, 2026-10-10): remembers which input a spread came from; intersected with
    # the plain one — both enclose, the meet is never wider. Not applied to a POINT reading (nothing to gain).
    if AFFINE and any(qs[n]["lo"] != qs[n]["hi"] if n not in piece else piece[n][0] != piece[n][1]
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
                    try:
                        derivs[n] = derivative(expr, n)
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
            r = _reading(expr, quantities, corner)
            if r is None:
                return False, f"{path}: no value at the corner"
            good = r[1] <= bound if op == "<=" else r[0] >= bound
            return (True, None) if good else (False, f"{path}: the extreme corner gives [{r[0]}, {r[1]}], not {op} {bound}")
        return False, f"{path}: unknown leaf {leaf!r}"

    ok, why = walk(cert, box, "")
    return (True, count[0]) if ok else (False, why)


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
    if op == "sqrt" or op in ("exp", "ln", "log10", "atan", "tan", "pow", "min", "max"):
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
