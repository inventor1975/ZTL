# -*- coding: utf-8 -*-
"""
THE BACKWARD PASS READ OFF THE TABLES — the same answer as `zbackward.backward`,
without listing the sets.

THE CURATOR'S QUESTION (2026-10-09): is the backward pass not the forward pass
read the other way? Measured the same day: one judge call costs 0.04-0.07 ms, so
the backward pass is no longer slow — it is BLIND past size four. It lists the
sets of grounds by size and stops at MAX_K = 4, so a conjunction of six
unverified grounds, whose answer is plainly "check all six", comes back as
"not searched further". Its own definition does not need the listing.

THE IDEA, AND WHY IT IS EXACT. For a set S of grounds, filled in every way (the
other grounds left unverified), each subformula takes a TYPE: the set of pairs
(its value now, the set of values it can take over every refinement of the
grounds still open) over the fillings of S. A connective's type follows from
its children's types by its table — on disjoint atoms the fillings and the
refinements of the two children are independent, so the image is exact. The
disposition is a function of the pair (checked against the judge in the stand):
EARNED  = (T, {T}),  REFUTED = (F, {F}),  ON CREDIT = (T, other),  OPEN = else.

The minimal sets are built bottom-up, per type: if S = S_A + S_B is minimal for
the parent, then S_A is minimal among the sets of A with the same type (a smaller
one would give the same parent type with a smaller S). So the minimal sets of
each type are products of the children's minimal sets, then the minimal ones
among those. No size cap; the work follows the answer's size, not 3^n.

SCOPE OF THIS FIRST TRANCHE, said aloud: an UNVERIFIED ground that occurs twice
breaks the independence. Such a formula is not handled here — `backward_tree`
returns None and the caller keeps `zbackward.backward`. (The forward grade
already handles repeats by enumerating only them, `zverify._values`; the same
can follow here.)
"""

import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from ztl import T, F, Z, ev           # noqa: E402

VALS = (T, F, Z)
BIN = ("and", "or", "imp", "xor", "xnor")
TABLE2 = {op: {(x, y): ev((op, "a", "b"), {"a": x, "b": y}) for x in VALS for y in VALS} for op in BIN}
TABLE1 = {"not": {x: ev(("not", "a"), {"a": x}) for x in VALS}}
MAX_FAMILY = 20000          # an antichain larger than this is refused aloud, not ground


class TooBig(Exception):
    pass


def disposition_of(cur, refset):
    if cur == T and refset == frozenset((T,)):
        return "EARNED"
    if cur == F and refset == frozenset((F,)):
        return "REFUTED"
    if cur == T:
        return "ON CREDIT"
    return "OPEN"


def _occurrences(phi, acc):
    if isinstance(phi, str):
        acc[phi] = acc.get(phi, 0) + 1
        return acc
    for c in phi[1:]:
        _occurrences(c, acc)
    return acc


def _minimal(sets):
    """The minimal elements (an antichain) of a collection of frozensets."""
    out = []
    for s in sorted(set(sets), key=len):
        if not any(o <= s for o in out):
            out.append(s)
    if len(out) > MAX_FAMILY:
        raise TooBig(len(out))
    return out


def _types(phi, marking, grounds):
    """{type: minimal sets} for the subformula. A type is a frozenset of
    (value now, frozenset of values over refinements) pairs over the fillings."""
    if isinstance(phi, str):
        v = marking.get(phi)
        if phi in grounds:
            open_ = frozenset([(Z, frozenset(VALS))])
            filled = frozenset([(T, frozenset((T,))), (F, frozenset((F,)))])
            return {open_: [frozenset()], filled: [frozenset((phi,))]}
        return {frozenset([(v, frozenset((v,)))]): [frozenset()]}
    op = phi[0]
    if op in TABLE1:
        tab = TABLE1[op]
        out = {}
        for t, fam in _types(phi[1], marking, grounds).items():
            nt = frozenset((tab[c], frozenset(tab[x] for x in r)) for c, r in t)
            out.setdefault(nt, []).extend(fam)
        return {t: _minimal(f) for t, f in out.items()}
    tab = TABLE2[op]
    A, B = _types(phi[1], marking, grounds), _types(phi[2], marking, grounds)
    out = {}
    for ta, fa in A.items():
        for tb, fb in B.items():
            nt = frozenset((tab[(ca, cb)], frozenset(tab[(x, y)] for x in ra for y in rb))
                           for ca, ra in ta for cb, rb in tb)
            out.setdefault(nt, []).extend(sa | sb for sa in fa for sb in fb)
    return {t: _minimal(f) for t, f in out.items()}


def backward_tree(phi, marking, target, by_disposition=True):
    """`zbackward.backward`'s families, computed from the tables. Returns the
    same dict shape (no size cap, never 'not searched further'), or None when the
    formula repeats an unverified ground (outside this tranche)."""
    grounds = tuple(a for a, v in sorted(marking.items()) if v == Z)
    occ = _occurrences(phi, {})
    if any(occ.get(a, 0) > 1 for a in grounds):
        return None
    gset = set(grounds)

    def hit(pair):
        o = disposition_of(*pair) if by_disposition else pair[0]
        return o in target if isinstance(target, (set, frozenset)) else o == target

    try:
        types = _types(phi, marking, gset)
        empty_type = next(t for t, fam in types.items() if frozenset() in fam)
        already = all(hit(p) for p in empty_type)       # no filling: one pair
        if already:
            return {"grounds": grounds, "already": True, "possible": [], "guaranteed": [],
                    "possible_none": False, "guaranteed_none": False, "target": target}
        poss = _minimal(s for t, fam in types.items() if any(hit(p) for p in t) for s in fam)
        guar = _minimal(s for t, fam in types.items() if all(hit(p) for p in t) for s in fam)
    except TooBig as e:
        return {"grounds": grounds, "already": False, "possible": [], "guaranteed": [],
                "possible_none": None, "guaranteed_none": None, "target": target,
                "отказ": f"a family of more than {MAX_FAMILY} minimal sets ({e.args[0]}): not listed"}
    # the atoms of a set are in the order zbackward reports them (sorted, as tuples)
    poss = [tuple(sorted(s)) for s in poss if s]
    guar = [tuple(sorted(s)) for s in guar if s]
    return {"grounds": grounds, "already": False, "possible": poss, "guaranteed": guar,
            "possible_none": not poss, "guaranteed_none": not guar, "target": target}
