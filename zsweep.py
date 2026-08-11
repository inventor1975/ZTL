# -*- coding: utf-8 -*-
"""
The census of arrows: all 19683 three-valued implications, mapped.

The literature enumerates implications inside well-behaved families —
Tomova's "natural implications" (2012), Robles & Méndez's natural
implicative expansions of Kleene's strong logic (2019-2021), the
Ciucci-Dubois map of connectives extending the Boolean ones (2013). Every
one of those families is fixed by criteria ZTL fails, so our kind of
arrow is excluded before the counting starts; and the standard remark
about the full space is that a complete description is intractable, which
stopped being true some decades ago. 19683 arrows times a dozen cheap
property checks is seconds.

The question this sweep is for is NOT "find a new logic" — empty cells in
a combinatorial space are usually junk, and we should expect junk. It is:

    ARE OUR LOSSES CHOSEN, OR FORCED?

The price list (12 laws alive, 14 fallen) reads as a series of decisions
the curator made. If instead no arrow whatsoever can combine our defining
principle with the lost law, then the loss was never a decision — it is
the shape of the space, and the price list becomes a list of theorems.

CONTROL, so the instrument is not trusted for free: restricted to
Tomova's three criteria the sweep must reproduce her published counts —
6 implications with D = {T}, 24 with D = {T, Z}. If it does not, nothing
else here may be believed.

Run:  python3 zsweep.py
"""
import os
import sys
from itertools import product

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from ztl import T, F, Z, NOT, AND, OR, IMP                    # noqa: E402

V = (T, F, Z)
CELLS = [(a, b) for a in V for b in V]          # the 9 cells, fixed order
ORDER = {F: 0, Z: 1, T: 2}                      # the linear order the
                                                # natural-implication
                                                # criteria presuppose


def arrow(table):
    """A binary connective as a lookup over the nine cells."""
    d = dict(zip(CELLS, table))
    return lambda a, b: d[(a, b)]


def all_arrows():
    for table in product(V, repeat=9):
        yield table


# ------------------------------------------------------------- properties
def c_extending(f):
    return all(f(a, b) == (T if (a == F or b == T) else F)
               for a in (T, F) for b in (T, F))


def normal(f, designated):
    """Łukasiewicz-Tarski normality: modus ponens preserves designation."""
    return all(not (a in designated and f(a, b) in designated)
               or b in designated for a, b in CELLS)


def order_condition(f, designated):
    return all(f(a, b) in designated
               for a, b in CELLS if ORDER[a] <= ORDER[b])


def identity(f, designated):
    return all(f(a, a) in designated for a in V)


def _forced(a, b):
    """Is the classical implication forced under every classical reading
    of the marks, each occurrence read independently?"""
    reads = {T: (True,), F: (False,), Z: (True, False)}
    return all((not x) or y for x in reads[a] for y in reads[b])


def no_credit(f, designated):
    """OUR defining principle as a property of the arrow alone: never
    designate a conditional whose truth is not FORCED under every reading
    of the marks. (The first draft of this predicate said 'never
    designate when the consequent is unverified' and the machine rejected
    our own arrow with it — F -> Z is designated here because falsity of
    the antecedent forces it, credit does not enter. The correction is
    recorded because the caricature was the author's, not the logic's.)
    Note it forbids granting credit but permits being STRICTER than
    forcing, so it is a real constraint and not a description of one
    table."""
    return all(_forced(a, b) or f(a, b) not in designated for a, b in CELLS)


def contraposition(f):
    return all(f(a, b) == f(NOT(b), NOT(a)) for a, b in CELLS)


def detachment_pool(f, designated):
    """Does the arrow internalise entailment? (the deduction theorem,
    checked on the one-premise fragment over a single variable)"""
    ok = True
    for phi in (lambda v: v, lambda v: NOT(v), lambda v: AND(v, v)):
        for psi in (lambda v: v, lambda v: NOT(v), lambda v: OR(v, NOT(v))):
            rule = all(psi(v) in designated
                       for v in V if phi(v) in designated)
            law = all(f(phi(v), psi(v)) in designated for v in V)
            if rule and not law:
                ok = False
    return ok


def profile(table, designated=(T,)):
    f = arrow(table)
    return {
        "C": c_extending(f),
        "MP": normal(f, designated),
        "ORD": order_condition(f, designated),
        "ID": identity(f, designated),
        "NOCREDIT": no_credit(f, designated),
        "CONTRA": contraposition(f),
        "DT": detachment_pool(f, designated),
    }


# ------------------------------------------------------------------ census
def sec1_control():
    print("-" * 72)
    print("1. CONTROL: reproduce Tomova's published counts, or stop here")
    n1 = sum(1 for t in all_arrows()
             if c_extending(arrow(t)) and normal(arrow(t), (T,))
             and order_condition(arrow(t), (T,)))
    n2 = sum(1 for t in all_arrows()
             if c_extending(arrow(t)) and normal(arrow(t), (T, Z))
             and order_condition(arrow(t), (T, Z)))
    print(f"   natural implications, D = {{T}}   : {n1}   (published: 6)")
    print(f"   natural implications, D = {{T, Z}}: {n2}   (published: 24)")
    assert n1 == 6 and n2 == 24
    print("   both match. The instrument counts what the literature counts,")
    print("   so its answers OUTSIDE that family may be read as measurements")
    print("   rather than as an artefact of our own encoding.")


def sec2_where_ztl_sits():
    print("-" * 72)
    print("2. WHERE OUR OWN ARROW SITS")
    ours = tuple(IMP(a, b) for a, b in CELLS)
    p = profile(ours)
    print(f"   ZTL's arrow: {p}")
    assert p["C"] and p["MP"] and p["NOCREDIT"]
    assert not p["ORD"] and not p["ID"]
    print("   classical on the verified, modus ponens intact, no free")
    print("   truth — and it fails the order condition and the identity law.")
    return ours


def sec3_forced_or_chosen():
    print("-" * 72)
    print("3. THE QUESTION: were the losses chosen, or forced?")
    # every arrow that is C-extending, keeps MP, and refuses free truth:
    # what else CAN it have?
    kin = [t for t in all_arrows()
           if c_extending(arrow(t)) and normal(arrow(t), (T,))
           and no_credit(arrow(t), (T,))]
    print(f"   arrows sharing our three commitments (classical on verified,")
    print(f"   modus ponens, no credit): {len(kin)}")
    with_id = [t for t in kin if identity(arrow(t), (T,))]
    with_ord = [t for t in kin if order_condition(arrow(t), (T,))]
    with_contra = [t for t in kin if contraposition(arrow(t))]
    with_dt = [t for t in kin if detachment_pool(arrow(t), (T,))]
    print(f"     ... of them, keeping the identity law p -> p : {len(with_id)}")
    print(f"     ... keeping Tomova's order condition          : {len(with_ord)}")
    print(f"     ... keeping contraposition                    : {len(with_contra)}")
    print(f"     ... internalising entailment (deduction thm)  : {len(with_dt)}")
    assert with_id == [] and with_ord == []
    print("   ZERO and ZERO. The identity law and the order condition are")
    print("   not available to ANY arrow that refuses credit — the loss was")
    print("   never a decision. p -> p at an unverified p is literally a")
    print("   conditional designated with an unexamined consequent, which is")
    print("   what 'no free truth' forbids. The price list is a list of")
    print("   theorems about the space, not of preferences.")
    return kin


def sec4_are_we_unique(kin, ours):
    print("-" * 72)
    print("4. AMONG THE SURVIVORS, ARE WE ONE OF MANY?")
    print(f"   arrows with our three commitments: {len(kin)} of 19683")
    profiles = {tuple(sorted(profile(t).items())) for t in kin}
    print(f"   distinct property profiles among them: {len(profiles)} — the")
    print("   commitments fix the properties and leave the table loose, so")
    print("   the seven properties above cannot single us out. Two further")
    print("   conditions can, and both are ours by construction:")
    # (a) two-valuedness of compounds: the arrow never returns the mark
    two_valued = [t for t in kin if Z not in t]
    # (b) maximality: designate T wherever the commitments permit it
    def maximal(t):
        f = arrow(t)
        for i, (a, b) in enumerate(CELLS):
            if f(a, b) != T and _forced(a, b):
                return False          # a forced cell left undesignated
        return True
    both = [t for t in two_valued if maximal(t)]
    print(f"     never returns the mark (compounds stay two-valued): "
          f"{len(two_valued)}")
    print(f"     ... and designates T in every cell where truth is FORCED: "
          f"{len(both)}")
    assert len(both) == 1 and both[0] == ours
    print("   EXACTLY ONE, and it is ours. So the table was not picked from")
    print("   seventy-two equals: given the three commitments, plus the")
    print("   demand that compounds carry no mark and that forced truth is")
    print("   never withheld, the arrow is UNIQUE. Every cell of it is a")
    print("   consequence; none of it is taste.")
    strictly_weaker = len(two_valued) - len(both)
    print(f"   the other {strictly_weaker} two-valued survivors are strictly")
    print("   stingier — they refuse truth that is forced, which is the")
    print("   mirror sin of granting truth that is not.")


if __name__ == "__main__":
    print("=" * 72)
    print("THE CENSUS OF ARROWS — 19683 implications, mapped")
    print("=" * 72)
    sec1_control()
    ours = sec2_where_ztl_sits()
    kin = sec3_forced_or_chosen()
    sec4_are_we_unique(kin, ours)
    print("=" * 72)
    print("ZSWEEP GREEN — the census reproduces the published counts of the")
    print("natural-implication family (6 and 24), which is the licence to")
    print("read the rest. And the rest says the losses were not chosen: no")
    print("arrow at all keeps the identity law or the order condition while")
    print("refusing to designate a conditional with an unexamined")
    print("consequent. The price list is a theorem about the space — and the")
    print("arrow itself is unique: three commitments, plus two-valued")
    print("compounds and no forced truth withheld, leave exactly one table")
    print("out of 19683, and it is the one the curator chose by hand.")
