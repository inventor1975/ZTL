# -*- coding: utf-8 -*-
"""The Lean reading for the kernel's Taylor coefficients (lean/ZJetRead.lean `CRead`), in exact fractions — the bridge
between zcertify.taylor_coeffs and the theorems ZJetRead.cread_sound / ZJetClose.taylorN_kernel (zero axioms, on VR's
operational reals).

taylor_coeffs reads f^(k)/k! over a piece by recurrences along the graph, rounding every step outward. CRead asks,
node by node, that each interval CONTAIN the exact interval the Lean recurrence builds from the kernel's own intervals
of the node's children (and of the node's lower coefficients):

  * a node without x: its value reading, then zeros;  x: (X, 1, 0, ...);  + − Σ: termwise;
  * ×: the interval convolution (corners per term, exact sums — the tightest witnesses of `CvB`);
  * ÷: q_{m+1} ⊇ (a_{m+1} − (q ∗ b')_m)·[1/b0], b0 clear of zero;  exp: e_{m+1} ⊇ (e ∗ D)_m/(m+1), D_t = (t+1)·a_{t+1};
  * sin/cos together: s_{m+1} ⊇ (c ∗ D)_m/(m+1), c_{m+1} ⊇ −(s ∗ D)_m/(m+1);  tan as sin/cos;
  * u^m (m a natural literal, u read ≥ 0): Miller's sum with the weights m(j+1) − (m+1)s combined, as the kernel sums;
  * √u (its value read > 0): s_1 ⊇ a_1·[1/(2 s0)], s_{j+2} ⊇ (a_{j+2} − (s' ∗ s')_j)·[1/(2 s0)], s' the series from 1.

The values (k = 0) of ÷, exp, sin, cos, tan, powers and of nodes without x are the kernel's value readings — Lean
VReads by the earlier bridges (lean/ZSlopeSqrt, ZTrig10-15 with ztrigcert in the run). Not in CRead: ln, log10, atan,
a non-natural exponent, a power of a base not read ≥ 0 (a node WITHOUT x may hold ln, log10).
"""
from fractions import Fraction as F

import zcertify as ZC

VALUE_OPS = {"add", "sub", "mul", "div", "exp", "ln", "sqrt", "log10", "sin", "cos", "tan", "sum", "pow"}


def _corners(a, b):
    ps = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return min(ps), max(ps)


def _scale(a, w):
    return _corners((F(w), F(w)), a)


def _cvb(A, B, m):
    """The exact interval convolution Σ_{j≤m} A_j·B_{m−j} (corners per term)."""
    lo = hi = F(0)
    for j in range(m + 1):
        l, h = _corners(A[j], B[m - j])
        lo, hi = lo + l, hi + h
    return lo, hi


def _hull(c, iv):
    return c[0] <= iv[0] and iv[1] <= c[1]


def _recip(b):
    """RecipOK's exact witnesses [1/hi, 1/lo] for b clear of zero, or None."""
    if b[0] <= 0 <= b[1]:
        return None
    return F(1) / b[1], F(1) / b[0]


def _val(node, quantities, piece):
    """The kernel's value reading of `node` over the piece, as taylor_coeffs' val() reads it."""
    import znum as _ZN
    q2 = dict(quantities)
    for nm, (lo, hi) in piece.items():
        q2[nm] = dict(quantities[nm], lo=lo, hi=hi)
    keep = _ZN._MEMO[0]
    _ZN._MEMO[0] = {}
    try:
        iv = _ZN._ev(node, q2)[0]
    except (ArithmeticError, ZeroDivisionError, KeyError, ValueError, TypeError):
        iv = None
    finally:
        _ZN._MEMO[0] = keep
    if iv is None or isinstance(iv[0], float) or isinstance(iv[1], float):
        return None
    return iv


def _value_covered(node, quantities, piece):
    """The node is in the grammar of Lean's value readings (VRead)."""
    if isinstance(node, (F, int)) or isinstance(node, str):
        return True
    op, *args = node
    if op not in VALUE_OPS:
        return False
    if op == "sum":
        return all(_value_covered(a, quantities, piece) for a in args[0])
    if op == "pow":
        base, c = args
        if not (isinstance(c, (F, int)) and F(c).denominator == 1 and c >= 0):
            return False
        r = _val(base, quantities, piece)
        return r is not None and r[0] >= 0 and _value_covered(base, quantities, piece)
    return all(_value_covered(a, quantities, piece) for a in args)


GRAMMAR = ("not in the Lean reading", "outside the value grammar", "value outside the grammar", "not a natural exponent",
           "base not read >= 0", "no series", "value not read > 0")


def check(expr, x, quantities, piece, n, cs, trace):
    """(True, "", False) when the kernel's series `cs` of `expr` (with `trace` from the same taylor_coeffs call)
    satisfies CRead to order n; else (False, why, fault) — fault: a node of the Lean grammar FAILS its inequality (the
    kernel's interval misses the Lean recurrence's), not merely a node outside the grammar."""
    Z = (F(0), F(0))
    names = {}
    seen = {}

    def nm(node):
        if node not in names:
            names[node] = ZC._names(node)
        return names[node]

    def series(node):
        if isinstance(node, tuple) and node[0] == "sum":
            parts = [series(a) for a in node[1]]
            if any(p is None for p in parts):
                return None
            return [ZC._iv_sum([p[k] for p in parts]) for k in range(n + 1)]
        if isinstance(node, (F, int)):
            v = F(node)
            return [(v, v)] + [Z] * n
        return trace.get(node)

    def sc_ok(u, a):
        s, c = trace.get(("sin", u)), trace.get(("cos", u))
        if s is None or c is None:
            return "sin/cos series not traced"
        D = [_scale(a[t + 1], t + 1) for t in range(n)]
        for m in range(n):
            if not _hull(s[m + 1], _scale(_cvb(c, D, m), F(1, m + 1))):
                return f"sin coefficient {m + 1}"
            if not _hull(c[m + 1], _scale(_cvb(s, D, m), F(-1, m + 1))):
                return f"cos coefficient {m + 1}"
        return ""

    def ok(node):
        key = node if not isinstance(node, list) else None
        if key is not None and key in seen:
            return seen[key]
        r = _ok(node)
        if key is not None:
            seen[key] = r
        return r

    def _ok(node):
        if isinstance(node, (F, int)):
            return ""
        if isinstance(node, str):
            return ""
        op, *args = node
        if x not in nm(node):
            return "" if _value_covered(node, quantities, piece) else f"{op}: a node without {x} outside the value grammar"
        c = series(node)
        if c is None:
            return f"{op}: no series traced"
        if op == "sum":
            for a in args[0]:
                w = ok(a)
                if w:
                    return w
            parts = [series(a) for a in args[0]]
            for k in range(n + 1):
                lo = sum((p[k][0] for p in parts), F(0))
                hi = sum((p[k][1] for p in parts), F(0))
                if not _hull(c[k], (lo, hi)):
                    return f"sum coefficient {k}"
            return ""
        if op in ("add", "sub", "mul", "div"):
            for a in args:
                w = ok(a)
                if w:
                    return w
            a, b = series(args[0]), series(args[1])
            if op == "add":
                return next((f"add coefficient {k}" for k in range(n + 1)
                             if not _hull(c[k], (a[k][0] + b[k][0], a[k][1] + b[k][1]))), "")
            if op == "sub":
                return next((f"sub coefficient {k}" for k in range(n + 1)
                             if not _hull(c[k], (a[k][0] - b[k][1], a[k][1] - b[k][0]))), "")
            if op == "mul":
                return next((f"mul coefficient {k}" for k in range(n + 1) if not _hull(c[k], _cvb(a, b, k))), "")
            if not _value_covered(node, quantities, piece):
                return "div: value outside the grammar"
            R = _recip(b[0])
            if R is None:
                return "div: divisor across zero"
            bs = b[1:]
            for m in range(n):
                cv = _cvb(c, bs, m)
                acc = (a[m + 1][0] - cv[1], a[m + 1][1] - cv[0])
                if not _hull(c[m + 1], _corners(acc, R)):
                    return f"div coefficient {m + 1}"
            return ""
        if op == "exp":
            w = ok(args[0])
            if w:
                return w
            if not _value_covered(node, quantities, piece):
                return "exp: value outside the grammar"
            a = series(args[0])
            D = [_scale(a[t + 1], t + 1) for t in range(n)]
            return next((f"exp coefficient {m + 1}" for m in range(n)
                         if not _hull(c[m + 1], _scale(_cvb(c, D, m), F(1, m + 1)))), "")
        if op in ("sin", "cos", "tan"):
            u = args[0]
            w = ok(u)
            if w:
                return w
            if not _value_covered(node, quantities, piece):
                return f"{op}: value outside the grammar"
            a = series(u)
            w = sc_ok(u, a)
            if w or op != "tan":
                return w
            s, co = trace[("sin", u)], trace[("cos", u)]
            R = _recip(co[0])
            if R is None:
                return "tan: cos across zero"
            cs1 = co[1:]
            for m in range(n):
                cv = _cvb(c, cs1, m)
                acc = (s[m + 1][0] - cv[1], s[m + 1][1] - cv[0])
                if not _hull(c[m + 1], _corners(acc, R)):
                    return f"tan coefficient {m + 1}"
            return ""
        if op == "pow":
            base, ce = args
            if not (isinstance(ce, (F, int)) and F(ce).denominator == 1 and ce >= 0):
                return "pow: not a natural exponent"
            w = ok(base)
            if w:
                return w
            if not _value_covered(node, quantities, piece):
                return "pow: base not read >= 0"
            m = int(ce)
            a = series(base)
            for j in range(n):
                W = [_scale(c[s], m * (j + 1) - (m + 1) * s) for s in range(j + 1)]
                R = _recip(_scale(a[0], j + 1))
                if R is None:
                    return "pow: base across zero"
                if not _hull(c[j + 1], _corners(_cvb(W, a[1:], j), R)):
                    return f"pow coefficient {j + 1}"
            return ""
        if op == "sqrt":
            w = ok(args[0])
            if w:
                return w
            if not _value_covered(node, quantities, piece):
                return "sqrt: value outside the grammar"
            if not c[0][0] > 0:
                return "sqrt: value not read > 0"
            a = series(args[0])
            R = _recip(_scale(c[0], 2))
            if n >= 1 and not _hull(c[1], _corners(a[1], R)):
                return "sqrt coefficient 1"
            cs1 = c[1:]
            for j in range(n - 1):
                cv = _cvb(cs1, cs1, j)
                acc = (a[j + 2][0] - cv[1], a[j + 2][1] - cv[0])
                if not _hull(c[j + 2], _corners(acc, R)):
                    return f"sqrt coefficient {j + 2}"
            return ""
        return f"{op}: not in the Lean reading"

    if cs is None:
        return False, "no series", False
    w = ok(expr)
    return (not w), w, bool(w) and not any(g in w for g in GRAMMAR)


def series_checked(expr, x, quantities, piece, n):
    """taylor_coeffs with its Lean check: (series or None, why-not-covered or "")."""
    trace = {}
    cs = ZC.taylor_coeffs(expr, x, quantities, piece, n, trace=trace)
    if cs is None:
        return None, "no series"
    good, why, _ = check(expr, x, quantities, piece, n, cs, trace)
    return cs, ("" if good else why)
