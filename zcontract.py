# -*- coding: utf-8 -*-
"""
HC4 — CONTRACTING A BOX BY A CONSTRAINT, EXACTLY. The kernel's proof that a requirement is met NOWHERE on a piece.

WHY (2026-10-18, the duel with dReal; the curator's "потом HC4"). zmin settles a piece by READING a requirement over
it: the reading's interval, past the bound, shows the requirement failing for every mix of the piece. A reading
loses to the dependency problem — `x*x - 2*x` over x in [0, 3] reads [-6, 9] although its least value is -1 — so a
piece where the requirement fails everywhere may still not be shown to, and the search splits on and on along the
feasibility boundary (blind 6 c07: 10 000 pieces left a plate undecided). dReal settles such pieces by CONTRACTION.

HOW (HC4-revise, Benhamou et al. 1999). The constraint `e op b` is read as "the value of e lies in T" (T = (-inf, b]
for <=, [b, inf) for >=, [b, b] for ==). A FORWARD pass reads every node of e over the box; a BACKWARD pass narrows,
from the root down, each node to what its parent allows — for z = a + b: a in z - b; for z = a * b: a in z / b when
b keeps away from 0; for z = exp(a): a in ln(z); and so on — and a QUANTITY'S box is met with every narrowing of
every one of its occurrences: that is what the reading cannot do. Repeated a fixed number of rounds (ROUNDS, a
count: no clock), stopping early when nothing moves. A box that becomes EMPTY: no point of it meets the constraint.

SOUND. Each projection keeps every solution: a point of the box where e meets T has, at every node, a value inside
the node's forward reading and inside what the backward step allows (lean/ZContract.lean proves each rule, and the
composition: a contraction keeps every solution; empty means none). Every interval is exact (fractions); the
functions' inverses are zfunc's outward brackets; every projected end is rounded OUTWARD onto a dyadic grid
(zfunc._down/_up) — a wider box keeps every solution. A node with no rule here narrows nothing (it is only read).
"""

from fractions import Fraction
import math

import zfunc as ZF

INF = float("inf")
ROUNDS = 8


class Empty(Exception):
    """The box holds no point meeting the constraint."""


def _out(lo, hi):
    """Rounded outward onto the dyadic grid (fractions kept small; wider is sound)."""
    lo = lo if isinstance(lo, float) else ZF._down(Fraction(lo))
    hi = hi if isinstance(hi, float) else ZF._up(Fraction(hi))
    return lo, hi


def _meet(a, b):
    lo, hi = max(a[0], b[0]), min(a[1], b[1])
    if lo > hi:
        raise Empty
    return lo, hi


def _m(x, y):
    """A product of two ends, 0 * inf taken as 0 (the end of a product of intervals)."""
    if x == 0 or y == 0:
        return Fraction(0)
    return x * y


def _add(a, b):
    return a[0] + b[0], a[1] + b[1]


def _sub(a, b):
    return a[0] - b[1], a[1] - b[0]


def _mul(a, b):
    c = [_m(x, y) for x in a for y in b]
    return min(c), max(c)


def _div(a, b):
    """a / b for b away from 0 (else the whole line)."""
    if b[0] <= 0 <= b[1]:
        return -INF, INF
    inv = (Fraction(1) / b[1] if not isinstance(b[1], float) else Fraction(0),
           Fraction(1) / b[0] if not isinstance(b[0], float) else Fraction(0))
    inv = (min(inv), max(inv))
    return _mul(a, inv)


def _const(n):
    return isinstance(n, (Fraction, int)) and not isinstance(n, bool)


def _fwd(n, dom, memo):
    """The node's reading over the box (memoised by identity: one value per occurrence)."""
    key = id(n)
    if key in memo:
        return memo[key][1]
    if isinstance(n, str):
        r = dom[n]
    elif _const(n):
        r = (Fraction(n), Fraction(n))
    elif isinstance(n, tuple) and n and n[0] in ("add", "sub", "mul", "div"):
        a, b = _fwd(n[1], dom, memo), _fwd(n[2], dom, memo)
        r = {"add": _add, "sub": _sub, "mul": _mul, "div": _div}[n[0]](a, b)
    elif isinstance(n, tuple) and n and n[0] == "sum":
        r = (Fraction(0), Fraction(0))
        for c in n[1]:
            r = _add(r, _fwd(c, dom, memo))
    elif isinstance(n, tuple) and n and n[0] == "neg":
        a = _fwd(n[1], dom, memo)
        r = (-a[1], -a[0])
    elif isinstance(n, tuple) and n and n[0] == "sqrt":
        a = _fwd(n[1], dom, memo)
        if a[1] < 0:
            raise Empty                          # never real: no point meets anything there
        lo = max(a[0], Fraction(0))
        r = (Fraction(0) if lo == 0 else _sqrt_lo(lo), INF if isinstance(a[1], float) else _sqrt_hi(a[1]))
    elif isinstance(n, tuple) and n and n[0] in _UNARY:
        a = _fwd(n[1], dom, memo)
        try:
            r = _UNARY[n[0]](a)
        except ZF.NoReadings:
            raise Empty                          # the function is undefined on the whole node's range
        if r is None:
            r = (-INF, INF)
    elif isinstance(n, tuple) and n and n[0] == "pow":
        a, b = _fwd(n[1], dom, memo), _fwd(n[2], dom, memo)
        try:
            r = ZF.iv_pow(a, b)
        except ZF.NoReadings:
            raise Empty
        if r is None:
            r = (-INF, INF)
    elif isinstance(n, tuple) and n and n[0] in ("min", "max"):
        a, b = _fwd(n[1], dom, memo), _fwd(n[2], dom, memo)
        r = (ZF.iv_min if n[0] == "min" else ZF.iv_max)(a, b)
    else:
        r = (-INF, INF)                          # no rule: read as anything (sound, narrows nothing)
    r = _out(*r)                                 # outward onto the grid: fractions stay small (wider is sound)
    memo[key] = (n, r)
    return r


_SQ = 32      # sqrt brackets on the grid 2^-32: integer square roots, exact and quick at any size


def _sqrt_lo(x):
    """A rational at most sqrt(x): isqrt(floor(x * 4^k)) / 2^k."""
    x = Fraction(x)
    return Fraction(math.isqrt((x.numerator << (2 * _SQ)) // x.denominator), 1 << _SQ)


def _sqrt_hi(x):
    """A rational at least sqrt(x)."""
    x = Fraction(x)
    r = math.isqrt(-((-(x.numerator << (2 * _SQ))) // x.denominator))     # isqrt(ceil(x * 4^k))
    s = Fraction(r, 1 << _SQ)
    return s if s * s >= x else s + Fraction(1, 1 << _SQ)


_UNARY = {"exp": ZF.iv_exp, "ln": ZF.iv_ln, "log10": ZF.iv_log10, "atan": ZF.iv_atan, "tan": ZF.iv_tan,
          "sin": ZF.iv_sin, "cos": ZF.iv_cos}


def _ln_iv(t):
    """An interval holding ln of every positive point of t ((-inf, ...) when t reaches 0)."""
    lo = -INF if t[0] <= 0 else ZF.iv_ln((Fraction(t[0]), Fraction(t[0])))[0]
    hi = INF if isinstance(t[1], float) else ZF.iv_ln((Fraction(t[1]), Fraction(t[1])))[1]
    return lo, hi


def _exp_iv(t):
    lo = Fraction(0) if isinstance(t[0], float) else ZF.iv_exp((Fraction(t[0]), Fraction(t[0])))[0]
    hi = INF if isinstance(t[1], float) else ZF.iv_exp((Fraction(t[1]), Fraction(t[1])))[1]
    return lo, hi


def _val(n, dom, memo):
    """A child's current value: a quantity's from the box (narrowed in place), a node's from the pass, a number."""
    if isinstance(n, str):
        return dom[n]
    if _const(n):
        return Fraction(n), Fraction(n)
    return memo[id(n)][1] if id(n) in memo else (-INF, INF)


def _bwd(n, t, dom, memo):
    """Narrow node n to t (what its parent allows), and its children accordingly."""
    if _const(n):
        if not t[0] <= n <= t[1]:
            raise Empty
        return
    if isinstance(n, str):
        dom[n] = _meet(dom[n], _out(*t))
        return
    if not isinstance(n, tuple) or id(n) not in memo:
        return
    z = _meet(memo[id(n)][1], _out(*t))
    memo[id(n)] = (n, z)
    op = n[0]
    if op in ("add", "sub", "mul", "div"):
        A, Bn = n[1], n[2]
        if op == "add":
            _bwd(A, _sub(z, _val(Bn, dom, memo)), dom, memo)
            _bwd(Bn, _sub(z, _val(A, dom, memo)), dom, memo)
        elif op == "sub":
            _bwd(A, _add(z, _val(Bn, dom, memo)), dom, memo)
            _bwd(Bn, _sub(_val(A, dom, memo), z), dom, memo)
        elif op == "mul":
            b = _val(Bn, dom, memo)
            if not (b[0] <= 0 <= b[1]):
                _bwd(A, _div(z, b), dom, memo)
            a = _val(A, dom, memo)
            if not (a[0] <= 0 <= a[1]):
                _bwd(Bn, _div(z, a), dom, memo)
        else:                                    # z = a / b: a = z * b; b = a / z (z away from 0)
            b = _val(Bn, dom, memo)
            if not (b[0] <= 0 <= b[1]):
                _bwd(A, _mul(z, b), dom, memo)
            a = _val(A, dom, memo)
            if not (z[0] <= 0 <= z[1]) and not (b[0] <= 0 <= b[1]):
                _bwd(Bn, _div(a, z), dom, memo)
    elif op == "sum":
        for k, c in enumerate(n[1]):
            rest = (Fraction(0), Fraction(0))
            for j, d in enumerate(n[1]):
                if j != k:
                    rest = _add(rest, _val(d, dom, memo))
            _bwd(c, _sub(z, rest), dom, memo)
    elif op == "neg":
        _bwd(n[1], (-z[1], -z[0]), dom, memo)
    elif op == "sqrt":                           # z = sqrt(a), z >= 0: a = z^2
        z = _meet(z, (Fraction(0), INF))
        _bwd(n[1], (z[0] * z[0], INF if isinstance(z[1], float) else z[1] * z[1]), dom, memo)
    elif op == "exp":                            # z = exp(a) > 0: a = ln z
        if z[1] <= 0:
            raise Empty
        _bwd(n[1], _ln_iv(z), dom, memo)
    elif op == "ln":                             # z = ln(a): a = exp z
        _bwd(n[1], _exp_iv(z), dom, memo)
    elif op == "log10":                          # z = ln(a)/ln 10: a = exp(z ln 10)
        _bwd(n[1], _exp_iv(_mul(z, ZF.LN10)), dom, memo)
    elif op == "atan":                           # z = atan(a), |z| < pi/2: a = tan z
        if -ZF.TAN_EDGE <= z[0] and z[1] <= ZF.TAN_EDGE:
            r = ZF.iv_tan((Fraction(z[0]), Fraction(z[1])))
            if r is not None:
                _bwd(n[1], r, dom, memo)
    elif op == "pow" and _const(n[2]) and n[2] != 0:
        c = Fraction(n[2])                       # z = a^c, a > 0: a = z^(1/c) (both monotone on a > 0)
        a = _val(n[1], dom, memo)
        if a[0] > 0:
            zp = _meet(z, (Fraction(0), INF))
            if zp[0] > 0 and not isinstance(zp[1], float):
                r = ZF.iv_pow((Fraction(zp[0]), Fraction(zp[1])), (1 / c, 1 / c))
                if r is not None:
                    _bwd(n[1], r, dom, memo)
    # other nodes (tan, sin, cos, min, max, pow with a variable exponent): read, never narrowed through


def contract(node, op, b, dom, rounds=ROUNDS):
    """The box `dom` ({name: (lo, hi)}) contracted by "node op b" being MET. -> the contracted box, or None when it is
    EMPTY (no point of the box meets the constraint)."""
    b = Fraction(b)
    target = {"<=": (-INF, b), ">=": (b, INF), "==": (b, b)}[op]
    dom = dict(dom)
    try:
        for _ in range(rounds):
            before = dict(dom)
            memo = {}
            _fwd(node, dom, memo)
            _bwd(node, target, dom, memo)
            if dom == before:
                break
    except Empty:
        return None
    return dom


def empty(node, op, b, qs):
    """True when no point of the box (zcertify's quantities {name: {"lo", "hi"}}) meets "node op b"."""
    dom = {n: (q["lo"], q["hi"]) for n, q in qs.items() if "lo" in q and "hi" in q}
    try:
        return contract(node, op, b, dom) is None
    except (KeyError, ZeroDivisionError, OverflowError, TypeError):
        return False                             # a name with no box, an unreadable node: not shown EMPTY
