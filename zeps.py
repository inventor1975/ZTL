# -*- coding: utf-8 -*-
"""
zeps — E34: Hilbert's ε-operator (indefinite descriptions), zero-trust.

E32 gave the DEFINITE description ιx.φ — "the x such that φ" — which
denotes only when a UNIQUE grounded individual satisfies φ. Its companion
is Hilbert's ε, the INDEFINITE description / choice term: εx.φ — "an x such
that φ", "SOME witness". Classically ε is the logical choice operator, with
the axiom

    φ(t) → φ(εx.φ)          (if anything is φ, the chosen witness is φ)

so that ∃x.φ ↔ φ(εx.φ). ZTL reads ε as an ACT: to choose a witness is to
earn one, and a choice from nothing is not an act — it is the mark. This is
the operational perimeter ("absence is never an act") and the curator's
"choice as an act", now at the level of terms.

THE MODEL. εx.φ picks a canonical grounded satisfier of φ; if φ has no
grounded satisfier the choice is unearned and εx.φ is a marked (non-
denoting) reference. Then:

FINDINGS (measured total over every predicate on the grounded domain):

  1. ε DENOTES IFF A WITNESS IS EARNED: E!(εx.φ) = T ⟺ some grounded x has
     φ(x)=T ⟺ ∃x.φ in ZTL (the strict-T existential of the quantifier
     layer). Existence of the choice term IS the existential — the ε–∃
     bridge, and in ZTL both are the same earned witness.

  2. THE ε-AXIOM holds for earned premises: whenever φ(t)=T for a grounded
     t, φ(εx.φ)=T. Through a marked t the premise is Z, so the axiom is
     vacuous — a choice is licensed only by an actual witness.

  3. ι AND ε SPLIT ON MULTIPLICITY. "The F" needs uniqueness, "an F" needs
     only existence: on a uniquely-satisfied φ they agree; on a MULTIPLY-
     satisfied φ, ιx.φ is marked (no unique referent) while εx.φ DENOTES
     (it may choose). On an empty φ both are marked.

  4. THE EMPTY CHOICE IS THE MARK. εx.(false) is a marked reference —
     choosing from nothing is not an act (the operational perimeter), so
     it earns no denotation, and E!(εx.false) = Z, never a free F.

  5. CHOICE IS AN ACT. Once εx.φ denotes, it is grounded and self-identical
     (E! = T, §24): the act of exhibiting a witness is exactly what grounds
     the term — nothing else does.

Run:  python3 zeps.py
"""
import os
import sys
from itertools import combinations

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from ztl import T, F, Z, IMP                                     # noqa: E402

GROUND = ("a", "b", "c")
MARK = "⊥"


def eps(phi):
    """εx.φ — a canonical grounded witness of φ, else a marked reference."""
    sat = [g for g in GROUND if phi(g) == T]
    return sat[0] if sat else MARK


def iota(phi):
    """ιx.φ — the unique grounded satisfier, else marked (E32)."""
    sat = [g for g in GROUND if phi(g) == T]
    return sat[0] if len(sat) == 1 else MARK


def denotes(t):
    return t in GROUND


def eqI(s, t):
    if not denotes(s) or not denotes(t):
        return Z
    return T if s == t else F


def Ebang(t):
    return eqI(t, t)


def exists_ztl(phi):
    """ZTL ∃x.φ — a strict T witness among the grounded (quantifiers.py)."""
    return T if any(phi(g) == T for g in GROUND) else F


# every predicate over the grounded domain, as a satisfied-set
ALL_PREDS = [ (lambda S: (lambda g: T if g in S else F))(set(s))
              for r in range(len(GROUND) + 1)
              for s in combinations(GROUND, r) ]


def satset(phi):
    return {g for g in GROUND if phi(g) == T}


if __name__ == "__main__":
    print("=" * 76)
    print("E34 — Hilbert's ε-operator (indefinite descriptions), zero-trust")
    print("=" * 76)
    print(f"  grounded domain {GROUND}; {len(ALL_PREDS)} predicates\n")

    # ------------------------------------------- 1. ε denotes iff ∃
    print("### 1. ε denotes ⟺ a witness is earned ⟺ ∃x.φ (ZTL)")
    bad = 0
    for phi in ALL_PREDS:
        lhs = (Ebang(eps(phi)) == T)
        rhs = (exists_ztl(phi) == T)
        if lhs != rhs:
            bad += 1
    print(f"    E!(εx.φ)=T  ⟺  ∃x.φ=T   over all predicates: "
          f"{bad} mismatches → {'HOLDS' if bad == 0 else 'FAILS'}")
    assert bad == 0, "the ε–∃ bridge failed"
    print("    the choice term denotes exactly when the existential is earned.")

    # ------------------------------------------- 2. the ε-axiom
    print("\n### 2. The ε-axiom φ(t) → φ(εx.φ), for earned premises")
    ax_bad = ax_checked = 0
    for phi in ALL_PREDS:
        e = eps(phi)
        for t in GROUND:
            if phi(t) == T:                       # earned premise
                ax_checked += 1
                phi_e = phi(e) if denotes(e) else Z
                if IMP(phi(t), phi_e) != T:
                    ax_bad += 1
    print(f"    φ(t)=T ⟹ φ(εx.φ)=T : {ax_bad} violations of {ax_checked} "
          f"earned premises → {'HOLDS' if ax_bad == 0 else 'FAILS'}")
    assert ax_bad == 0, "the ε-axiom failed on an earned premise"

    # ------------------------------------------- 3. ι vs ε on multiplicity
    print("\n### 3. ι vs ε — 'the F' (unique) vs 'an F' (some)")
    agree = split = 0
    example_split = None
    for phi in ALL_PREDS:
        n = len(satset(phi))
        i, e = iota(phi), eps(phi)
        if n == 1:
            assert i == e, "ι and ε disagreed on a unique predicate"
            agree += 1
        elif n >= 2:
            # ι marked, ε denotes
            assert not denotes(i) and denotes(e), "ι/ε multiplicity split broke"
            split += 1
            if example_split is None:
                example_split = (satset(phi), i, e)
    print(f"    unique φ: ι = ε (agree), {agree} predicates")
    print(f"    multiple φ: ι marked, ε denotes, {split} predicates")
    S, i, e = example_split
    print(f"    e.g. φ satisfied by {sorted(S)}: ιx.φ = {i} (marked), "
          f"εx.φ = {e} (a choice)")

    # ------------------------------------------- 4. empty choice = mark
    print("\n### 4. The empty choice is the mark — 'absence is never an act'")
    empty = lambda g: F
    e0 = eps(empty)
    print(f"    εx.(false) denotes: {denotes(e0)}  → E!(εx.false) = {Ebang(e0)}")
    assert not denotes(e0) and Ebang(e0) == Z, "empty ε was not marked/Z"
    print("    choosing from nothing earns no denotation: Z, never a free F")
    print("    (the operational perimeter, and choice-as-act).")

    # ------------------------------------------- 5. choice is an act
    print("\n### 5. Choice is an act — a denoting ε is self-identical")
    nonempty = [phi for phi in ALL_PREDS if satset(phi)]
    assert all(Ebang(eps(phi)) == T for phi in nonempty), \
        "a witnessed ε failed self-identity"
    print(f"    every witnessed εx.φ is grounded and self-identical (E!=T),")
    print(f"    {len(nonempty)} predicates — the act of exhibiting the witness")
    print(f"    is what grounds the term, nothing else.")

    print("\n" + "=" * 76)
    print("WHAT E34 ADDS")
    print("=" * 76)
    print("  Hilbert's ε as the zero-trust CHOICE term, the companion to")
    print("  E32's ι. It denotes exactly when a witness is earned — which is")
    print("  ZTL's own ∃ — so the ε–∃ bridge is the identity of two earned")
    print("  witnesses. ι and ε divide the labour of reference: 'the F' wants")
    print("  uniqueness and marks on multiplicity, 'an F' wants only a")
    print("  witness and chooses. And the empty choice is the mark: to pick")
    print("  from nothing is not an act, so it earns Z — choice is an act,")
    print("  the operational perimeter at the level of terms.")
    print("\n  ZEPS GREEN — ε = earned choice; ε denotes ⟺ ∃; empty choice → Z.")
