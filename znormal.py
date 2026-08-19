# -*- coding: utf-8 -*-
"""
znormal — the normal form, and what it costs.

A verdict of `T` can rest on a mark: a ground nobody verified reads as `F` under
a negation, and that `F` can carry a `T` upward. `zverify.grade` already names
such a verdict `until-verification`. This module says what to DO about it.

    normalise(phi)      expand xor/xnor by their proved definitions, then push
                        negations down to the atoms
    on_credit(phi, env) True when the verdict is T as written and stops being T
                        once normalised — i.e. it was resting on the mark

NORMALISATION IS NOT AN EQUIVALENCE HERE, and that is the point. De Morgan
fails in this calculus (`deMorgan1_fails`), so the normalised formula is a
DIFFERENT, strictly weaker one. Two theorems in `lean/ContextClosure.lean` fix
both sides of the trade:

    normal_form_sound        in normal form no verdict is granted that a
                             completion of the withheld ground could defeat
    normal_form_incomplete   and verdicts every completion upholds are lost —
                             `b ∨ ¬b` is the witness, because the excluded
                             middle fails here by construction

Measured on a census of formulas of depth <= 2 over two atoms
(`veraxis/context-closure-001/normalize.py`): all 983 credit-verdicts vanish,
369 honest ones go with them — 2.66 lies discarded per honest verdict lost —
and on fully verified data nothing changes at all (11,624 comparisons, zero
disagreements), because where nothing carries the mark ZTL is classical logic
formula for formula.

So this is a lever, not a fix: it buys "never grant what the unverified could
overturn" and it spends "never lose what every completion upholds". Which of
those two errors matters more is not a question this file can answer.
"""

from ztl import T, ev

__all__ = ["expand", "nnf", "normalise", "on_credit"]


def expand(phi):
    """Expand xor/xnor by the corpus's own proved definitions — `xor_def` and
    `xnor_def` in `lean/ZTL.lean`. These ARE equivalences in ZTL."""
    if isinstance(phi, str):
        return phi
    op = phi[0]
    if op == "not":
        return ("not", expand(phi[1]))
    x, y = expand(phi[1]), expand(phi[2])
    if op == "xor":
        return ("or", ("and", x, ("not", y)), ("and", ("not", x), y))
    if op == "xnor":
        return ("or", ("and", x, y), ("and", ("not", x), ("not", y)))
    return (op, x, y)


def nnf(phi, neg=False):
    """Push negations to the atoms by the CLASSICAL rules. Not an equivalence
    in ZTL — see the module docstring."""
    if isinstance(phi, str):
        return ("not", phi) if neg else phi
    op = phi[0]
    if op == "not":
        return nnf(phi[1], not neg)
    if op == "and":
        return (("or" if neg else "and"), nnf(phi[1], neg), nnf(phi[2], neg))
    if op == "or":
        return (("and" if neg else "or"), nnf(phi[1], neg), nnf(phi[2], neg))
    if op == "imp":
        if neg:
            return ("and", nnf(phi[1], False), nnf(phi[2], True))
        return ("or", nnf(phi[1], True), nnf(phi[2], False))
    return ("not", phi) if neg else phi


def normalise(phi):
    return nnf(expand(phi))


def on_credit(phi, env):
    """Is this `T` resting on the mark?

    True when the formula reads `T` as written and no longer does once
    normalised. Such a verdict was carried by an unverified ground reading as
    false under a negation — the shape `zverify.grade` calls
    `until-verification`, here with the cause named and the remedy shown."""
    if ev(phi, env) != T:
        return False
    return ev(normalise(phi), env) != T
