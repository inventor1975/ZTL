# -*- coding: utf-8 -*-
"""
zread — the dirty reading and the forced outcome, from ZTL alone (pure branch, curator 2026-11-22).

Mirror of Lean `ZRead` / `ZForced`. Each OCCURRENCE of an unverified atom is read on its own (the canon of the
dirty parameter). `reach(phi, v)` = (can_be_true, can_be_false): which classical values the readings of the
occurrences reach. Readings of a compound are the products of the readings of its parts, so the count is one
pass (Lean `foC_eq_fo`: the one-pass count IS the reading).

    forced(phi, v) = T   every reading true   (the judge's EARNED)
                   = F   every reading false  (REFUTED)
                   = N   not forced           (the solver's phase "not yet computed"; never the mark Z)

An atom whose value is Z (the mark) or N (an own sentence not yet determined) reaches both. No strong Kleene
table is defined or used here; the connective rules of `forced` are derived (Lean `fo_neg`, `fo_conj`, …).
"""
from ztl import T, F, Z, VALUES

N = "N"

_G = {"and": lambda a, b: a and b, "or": lambda a, b: a or b, "imp": lambda a, b: (not a) or b,
      "xor": lambda a, b: a != b, "xnor": lambda a, b: a == b}


def _atom(x):
    return (x == T or x in (Z, N), x == F or x in (Z, N))


def _comb(g, p, q):
    t = f = False
    for a in (True, False):
        if not (p[0] if a else p[1]):
            continue
        for c in (True, False):
            if not (q[0] if c else q[1]):
                continue
            if g(a, c):
                t = True
            else:
                f = True
    return (t, f)


def reach(phi, v):
    """(can be true, can be false) over the independent readings of the occurrences."""
    if isinstance(phi, str):
        return _atom(phi if phi in VALUES or phi == N else v[phi])
    op = phi[0]
    if op == "not":
        t, f = reach(phi[1], v)
        return (f, t)
    return _comb(_G[op], reach(phi[1], v), reach(phi[2], v))


def outcome(p):
    t, f = p
    return T if t and not f else F if f and not t else N


def forced(phi, v):
    """T / F if forced under every reading of every occurrence, else N."""
    return outcome(reach(phi, v))


def ph_not(a):
    return {T: F, F: T, N: N}[a]


if __name__ == "__main__":
    # the curator's examples (2026-11-22)
    assert forced(("xnor", "x", "x"), {"x": Z}) == N          # x <-> x: not forced (classically true)
    assert forced(("and", "s", ("not", "s")), {"s": Z}) == N  # not forced; F in every cleaning
    assert forced(("not", "J"), {"J": Z}) == N
    assert forced(("or", "x", "T"), {"x": Z}) == T
    print("zread: ok")
