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


# ------------------------------------------------------------------ classics first, in ONE place
# curator 2026-11-22: "first classics; if classics gives no answer, then Z and ZTL's verdicts". Both the judge
# (its dispositions) and the passport (its grounding step) call THIS, and nothing else decides it.

def _occ(phi, acc):
    if isinstance(phi, str):
        if phi not in VALUES and phi != N:
            acc[phi] = acc.get(phi, 0) + 1
    else:
        for x in phi[1:]:
            _occ(x, acc)
    return acc


def stable(phi, v, cap=None):
    """Classics with ONE value per atom: T (F) if phi is classically true (false) under every classical value
    of every atom still open in v (the mark Z or the phase N), else N. None when the repeated open atoms exceed
    `cap`. Exact and cheap: only atoms occurring more than once are enumerated; with them fixed every other
    open atom occurs once, where the reading of its occurrences IS its completion (Lean `ZRead`), so one
    `forced` pass decides the rest."""
    occ = _occ(phi, {})
    open_rep = sorted(a for a, k in occ.items() if k > 1 and v.get(a, Z) in (Z, N))
    if cap is not None and len(open_rep) > cap:
        return None
    from itertools import product
    seen = set()
    for bits in product((T, F), repeat=len(open_rep)):
        r = forced(phi, {**v, **dict(zip(open_rep, bits))})
        seen.add(r)
        if N in seen or len(seen) > 1:
            return N
    return seen.pop()


def settle(phi, v, cap=None):
    """The one decision: (forced, stable). forced = T/F/N by every reading of every occurrence (EARNED /
    REFUTED); stable = T/F/N (or None over the cap) by every completion (IF STABLE). When both are N, classics
    has no answer and the VERDICT is ZTL's greedy table — not decided here."""
    return forced(phi, v), stable(phi, v, cap)


if __name__ == "__main__":
    # the curator's examples (2026-11-22)
    assert forced(("xnor", "x", "x"), {"x": Z}) == N          # x <-> x: not forced (classically true)
    assert forced(("and", "s", ("not", "s")), {"s": Z}) == N  # not forced; F in every cleaning
    assert forced(("not", "J"), {"J": Z}) == N
    assert forced(("or", "x", "T"), {"x": Z}) == T
    assert stable(("xnor", "x", "x"), {"x": Z}) == T                    # x <-> x: classically true
    assert stable(("and", "s", ("not", "s")), {"s": Z}) == F            # classically false
    assert stable(("not", "J"), {"J": Z}) == N                          # classics gives no answer: waits on J
    assert stable(("or", "J", ("not", "J")), {"J": Z}) == T
    print("zread: ok")
