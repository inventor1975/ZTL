# -*- coding: utf-8 -*-
"""The Lean reading for the kernel's MONOTONE leaf (lean/ZMonoStep.lean: slope_step, monotone_leaf_up/down_step), in
exact fractions — the bridge between zintegral's {"monotone": "+"|"-"} leaf and the theorems (zero axioms).

The kernel reads the sign of ITS symbolic derivative (zcertify.derivative) with its full reading (affine forms, ...).
The theorem asks instead:
  * a STEP READING of f over the piece (ZDeriv.StepRead, constructor by constructor): every factor and its derivative
    bounded on the box (a naive VRead), divisors and cos under tan clear of zero, √'s value read > 0;
  * a box bound of the GRAMMAR's derivative D f (lean_D mirrors ZDeriv.D, no simplification) with the sign: the naive
    reading, the checked affine one (zaffinecert), or their meet (ZAffine.boxEv_meet).
atan (2026-10-17): StepRead.atan — its step from ZAtan.ustep_atan (the grid sum of 1/(1 + t²)). u^c with c not a natural literal is exp(c·ln u).
"""
from fractions import Fraction as F

import zcertify as ZC
import ztaylorcert as T
import zaffinecert as AC

Z, O = F(0), F(1)


class NotStep(Exception):
    pass


def lean_D(e, x):
    """ZDeriv.D on the kernel's nodes (a natural literal exponent read as powN; a sum as nested adds)."""
    if isinstance(e, (int, F)):
        return Z
    if isinstance(e, str):
        return O if e == x else Z
    op, *a = e
    if op == "sum":
        out = Z
        for t in a[0]:
            out = ("add", out, lean_D(t, x))
        return out
    if op == "add":
        return ("add", lean_D(a[0], x), lean_D(a[1], x))
    if op == "sub":
        return ("sub", lean_D(a[0], x), lean_D(a[1], x))
    if op == "mul":
        return ("add", ("mul", lean_D(a[0], x), a[1]), ("mul", a[0], lean_D(a[1], x)))
    if op == "div":
        return ("div", ("sub", ("mul", lean_D(a[0], x), a[1]), ("mul", a[0], lean_D(a[1], x))), ("mul", a[1], a[1]))
    if op == "exp":
        return ("mul", e, lean_D(a[0], x))
    if op == "ln":
        return ("div", lean_D(a[0], x), a[0])
    if op == "log10":
        return ("div", lean_D(a[0], x), ("mul", a[0], ("ln", F(10))))
    if op == "sqrt":
        return ("div", lean_D(a[0], x), ("mul", F(2), e))
    if op == "sin":
        return ("mul", ("cos", a[0]), lean_D(a[0], x))
    if op == "cos":
        return ("mul", ("sub", Z, ("sin", a[0])), lean_D(a[0], x))
    if op == "tan":
        return ("mul", ("add", O, ("mul", e, e)), lean_D(a[0], x))
    if op == "pow" and isinstance(a[1], (int, F)) and F(a[1]).denominator == 1 and a[1] >= 0:
        k = int(a[1])
        if k == 0:
            return Z
        return ("mul", ("mul", F(k), ("pow", a[0], F(k - 1))), lean_D(a[0], x))
    if op == "pow":
        return lean_D(T.lean_node(e), x)                 # u^c = exp(c·ln u)
    if op == "atan":
        return ("div", lean_D(a[0], x), ("add", O, ("mul", a[0], a[0])))
    raise NotStep(f"{op}: no D in the grammar")


def _names(e):
    return ZC._names(e)


def step_ok(e, x, qs, piece):
    """"" when a ZDeriv.StepRead of e exists over the box (its premises read), else why not."""
    def bd(n):
        if not T._value_covered(n, qs, piece):
            raise NotStep(f"{n[0] if isinstance(n, tuple) else n}: no Lean value reading")
        r = T._naive(n, qs, piece)  # bd(): _value_covered checked just above
        if r is None:
            raise NotStep(f"{n[0] if isinstance(n, tuple) else n}: no reading on the box")
        return r

    def clear(n):
        r = bd(n)
        if r[0] <= 0 <= r[1]:
            raise NotStep(f"a divisor read across zero")

    def go(n):
        if isinstance(n, (int, F)) or isinstance(n, str):
            return                                     # const, var
        if x not in _names(n):
            return                                     # StepRead.free
        op, *a = n
        if op == "sum":
            for t in a[0]:
                go(t)
            return
        if op in ("add", "sub"):
            go(a[0]); go(a[1]); return
        if op == "mul":
            go(a[0]); go(a[1])
            for t in (a[0], a[1], lean_D(a[0], x), lean_D(a[1], x)):
                bd(t)
            return
        if op == "div":
            go(a[0]); go(a[1])
            bd(a[0]); clear(a[1]); bd(lean_D(a[0], x)); bd(lean_D(a[1], x))
            return
        if op in ("exp", "sin", "cos"):
            go(a[0])
            bd(a[0]); bd(lean_D(a[0], x))
            bd({"exp": n, "sin": ("cos", a[0]), "cos": ("sin", a[0])}[op])
            return
        if op == "tan":
            go(("div", ("sin", a[0]), ("cos", a[0])))
            clear(("cos", a[0]))
            return
        if op == "sqrt":
            go(a[0])
            r = bd(a[0])
            if r[0] < 0:
                raise NotStep("sqrt: its argument read below 0")
            s = bd(n)
            if not s[0] > 0:
                raise NotStep("sqrt: its value not read > 0")
            bd(lean_D(a[0], x))
            return
        if op == "pow" and isinstance(a[1], (int, F)) and F(a[1]).denominator == 1 and a[1] >= 0:
            if a[1] == 0:
                return
            go(a[0]); bd(a[0]); bd(lean_D(a[0], x))
            return
        if op == "pow":
            go(T.lean_node(n))
            return
        if op == "ln":
            go(a[0])
            r = bd(a[0])
            if not r[0] > 0:
                raise NotStep("ln: its argument not read > 0")
            bd(lean_D(a[0], x))
            return
        if op == "log10":
            go(("ln", a[0]))
            r = bd(a[0])
            if not r[0] > 0:
                raise NotStep("log10: its argument not read > 0")
            if not bd(("ln", F(10)))[0] > 0:
                raise NotStep("log10: ln 10 not read > 0")
            return
        if op == "atan":
            go(a[0]); bd(a[0]); bd(lean_D(a[0], x))
            return
        raise NotStep(f"{op}: not in StepRead")

    try:
        go(e)
    except NotStep as ns:
        return str(ns)
    return ""


def lean_D_reading(f, x, qs, piece):
    """((lo, hi), "") — a box bound Lean proves for D_x f with a step reading of f along x (ZDeriv.StepRead), or
    (None, why)."""
    if x not in _names(f):
        return (F(0), F(0)), ""                          # StepRead.free; ZDeriv.D_free: D_x f is exactly 0
    try:
        d = lean_D(f, x)
    except NotStep as ns:
        return None, str(ns)
    w = step_ok(f, x, qs, piece)
    if w:
        return None, "no step reading: " + w
    nv = T.lean_naive(d, qs, piece)
    q2 = dict(qs)
    for n_, (lo, hi) in piece.items():
        q2[n_] = dict(qs[n_], lo=lo, hi=hi)
    try:
        av, _ = AC.read_checked(d, qs, piece, ZC._rat_sqrt, lambda n: ZC._plain(n, q2), lambda n: T.lean_naive(n, qs, piece))
    except RecursionError:
        av = None
    cands = [iv for iv in (nv, av) if iv is not None]
    if not cands:
        return None, "D f: no Lean reading"
    return (max(iv[0] for iv in cands), min(iv[1] for iv in cands)), ""


def sign_covered(f, x, qs, piece, sign):
    """"" when Lean proves the monotone leaf's sign over the piece (ZMonoStep), else why not."""
    try:
        d = lean_D(f, x)
    except NotStep as ns:
        return str(ns)
    w = step_ok(f, x, qs, piece)
    if w:
        return "no step reading: " + w
    nv = T.lean_naive(d, qs, piece)
    q2 = dict(qs)
    for n_, (lo, hi) in piece.items():
        q2[n_] = dict(qs[n_], lo=lo, hi=hi)
    try:
        av, why = AC.read_checked(d, qs, piece, ZC._rat_sqrt, lambda n: ZC._plain(n, q2), lambda n: T.lean_naive(n, qs, piece))
    except RecursionError:
        av, why = None, "too deep"
    cands = [iv for iv in (nv, av) if iv is not None]
    if not cands:
        return "D f: no Lean reading"
    lo = max(iv[0] for iv in cands)
    hi = min(iv[1] for iv in cands)
    if (sign == "+" and lo >= 0) or (sign == "-" and hi <= 0):
        return ""
    return f"D f's Lean reading [{float(lo):.3g}, {float(hi):.3g}] does not keep the sign {sign}"
