# -*- coding: utf-8 -*-
"""
zeq — E31: EQUALITY with Leibniz substitution, under the zero-trust lift.

Classical first-order logic has identity: a two-place predicate `a = b`
with reflexivity (a = a) and Leibniz's law / substitutivity of identicals
(a = b ⟹ φ(a) ↔ φ(b)). ZTL's first-order layer (quantifiers.py, zfo.py)
never had it. This stand adds it — and the zero-trust principle turns the
identity axioms from free laws into EARNED verdicts.

THE MODEL (the native reading). Individuals of the domain are references.
A *grounded* individual is a verified reference; a *marked* individual is
one whose reference is not yet earned (a null pointer, an unresolved
description, 1/0 — the individual-level face of Z). Then equality is an
atomic predicate whose value is:

    Eq(a, b) = T   if a, b are grounded and denote the same object
             = F   if a, b are grounded and denote different objects
             = Z   if a or b is a marked (unverified) reference.

A generic predicate P likewise reads a marked reference as Z: an atomic
statement about an unresolved reference is on credit, P(marked) = Z.
(The mark-detector isZ is a meta-predicate, not a generic P; Leibniz is
about generic predicates.)

WHAT THE ZERO-TRUST LIFT DOES TO THE IDENTITY AXIOMS (all MEASURED):

  1. REFLEXIVITY falls on the mark. Eq(a,a) = T for grounded a, but Z for
     marked a — self-identity is not free; an unresolved reference is not
     even certified equal to itself. This is exactly zfuncs ("even id is
     not certified on a marked argument"), zopsets/reals ("identity on a
     marked value does not certify"), E8 ("1/0 = 1/0 → Z"), now at the
     level of the logic's own = predicate.

  2. SYMMETRY splits rule vs law. As a RULE, Eq(a,b) ⊨ Eq(b,a) holds
     totally. As a biconditional LAW, Eq(a,b) ↔ Eq(b,a) FAILS whenever the
     equality is Z, because ↔ over Z is F (quarantine is detectable:
     ↔(Z,Z) = F). The same rule/law split entailment.py already found.

  3. LEIBNIZ SUBSTITUTIVITY survives as a rule — salva veritate but not
     salva Z. Eq(a,b) ⊨ P(a) ↔ P(b) for every generic predicate P: when
     the equality is EARNED (T), a and b are the same grounded object and
     P agrees; where a reference is unverified the equality is never T, so
     the substitution is simply never licensed. You cannot launder a mark
     through identity.

  4. IDENTITY OF INDISCERNIBLES fails for the mark. Two distinct marked
     references give Z under every generic predicate — indiscernible — yet
     Eq(m1,m2) = Z, not T. Unverified references are not made equal by the
     mere absence of a distinguishing predicate.

So ZTL keeps FO identity as a consequence relation (Leibniz, symmetry,
transitivity all hold as rules for earned equalities) and loses exactly
the free half — reflexivity-on-credit and indiscernibility-on-credit —
by the same coin as everywhere else: a verdict is never granted on an
unearned reference.

Run:  python3 zeq.py
"""
import os
import sys
from itertools import product

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from ztl import T, F, Z, NOT, AND, OR, XNOR                     # noqa: E402

# ---- individuals: grounded tokens g0,g1,g2 ; marked references m1,m2 ----
GROUND = ("g0", "g1", "g2")
MARKED = ("m1", "m2")            # two distinct UNRESOLVED references
INDIV = GROUND + MARKED


def is_marked(x):
    return x in MARKED


def Eq(a, b):
    """The identity predicate, zero-trust."""
    if is_marked(a) or is_marked(b):
        return Z                       # reference unverified → on credit
    return T if a == b else F


def pred(subset):
    """A generic predicate: holds (T) of grounded individuals in `subset`,
    fails (F) of the other grounded ones, and is Z of any marked one."""
    def P(x):
        if is_marked(x):
            return Z                   # atomic fact about an unresolved ref
        return T if x in subset else F
    return P


# every generic predicate over the grounded individuals
ALL_PREDS = [pred(set(s))
             for r in range(len(GROUND) + 1)
             for s in __import__("itertools").combinations(GROUND, r)]


if __name__ == "__main__":
    print("=" * 76)
    print("E31 — EQUALITY with Leibniz substitution, zero-trust")
    print("=" * 76)
    print(f"  domain: grounded {GROUND}, marked {MARKED}; "
          f"{len(ALL_PREDS)} generic predicates\n")

    # ---------------------------------------------------- 1. reflexivity
    print("### 1. Reflexivity a = a — earned, falls on the mark")
    refl = {a: Eq(a, a) for a in INDIV}
    for a in INDIV:
        print(f"    Eq({a},{a}) = {refl[a]}"
              + ("  (marked → on credit)" if is_marked(a) else ""))
    assert all(refl[a] == T for a in GROUND), "reflexivity broke on grounded"
    assert all(refl[a] == Z for a in MARKED), "self-identity certified a mark"
    print("    grounded: T total; marked: Z total — self-identity is earned.")

    # ---------------------------------------------------- 2. symmetry
    print("\n### 2. Symmetry — rule holds, biconditional law falls on Z")
    rule_bad = sum(1 for a in INDIV for b in INDIV
                   if Eq(a, b) == T and Eq(b, a) != T)
    law_fail = [(a, b) for a in INDIV for b in INDIV
                if XNOR(Eq(a, b), Eq(b, a)) != T]
    print(f"    rule  Eq(a,b) ⊨ Eq(b,a): {rule_bad} violations → "
          f"{'HOLDS' if rule_bad == 0 else 'FAILS'}")
    print(f"    law   Eq(a,b) ↔ Eq(b,a): {len(law_fail)} non-T cells "
          f"(all where the equality is Z, since ↔(Z,Z)=F)")
    assert rule_bad == 0, "symmetry failed as a rule"
    assert law_fail and all(Eq(a, b) == Z for a, b in law_fail), \
        "the law failed somewhere the equality was NOT Z"
    print("    → the rule/law split, on identity itself.")

    # ---------------------------------------------------- 3. transitivity
    print("\n### 3. Transitivity — rule holds")
    trans_bad = sum(1 for a in INDIV for b in INDIV for c in INDIV
                    if Eq(a, b) == T and Eq(b, c) == T and Eq(a, c) != T)
    print(f"    Eq(a,b), Eq(b,c) ⊨ Eq(a,c): {trans_bad} violations → "
          f"{'HOLDS' if trans_bad == 0 else 'FAILS'}")
    assert trans_bad == 0, "transitivity failed as a rule"

    # ---------------------------------------------------- 4. Leibniz
    print("\n### 4. Leibniz substitutivity — salva veritate, not salva Z")
    leib_checked = leib_bad = 0
    licensed = 0
    for a in INDIV:
        for b in INDIV:
            e = Eq(a, b)
            for P in ALL_PREDS:
                leib_checked += 1
                # rule: Eq(a,b) ⊨ P(a) ↔ P(b)
                if e == T:
                    licensed += 1
                    if XNOR(P(a), P(b)) != T:
                        leib_bad += 1
    print(f"    Eq(a,b) ⊨ P(a)↔P(b) over {len(ALL_PREDS)} predicates: "
          f"{leib_bad} violations of {licensed} licensed substitutions "
          f"→ {'HOLDS' if leib_bad == 0 else 'FAILS'}")
    print("    substitution is licensed ONLY where equality is earned (T);")
    print("    through a marked reference Eq is never T, so no laundering.")
    assert leib_bad == 0, "Leibniz substitutivity failed for an earned equality"

    # ---------------------------------- 5. identity of indiscernibles
    print("\n### 5. Identity of indiscernibles — fails for the mark")
    def indiscernible(a, b):
        return all(P(a) == P(b) for P in ALL_PREDS)
    witness = None
    for a in INDIV:
        for b in INDIV:
            if a != b and indiscernible(a, b) and Eq(a, b) != T:
                witness = (a, b)
                break
        if witness:
            break
    print(f"    m1,m2 indiscernible (both Z under every P): "
          f"{indiscernible('m1', 'm2')}")
    print(f"    yet Eq(m1,m2) = {Eq('m1','m2')}  → identicals-of-indiscernibles"
          f" FAILS on marks")
    assert witness is not None, "expected an indiscernible-but-unequal pair"
    print(f"    witness: {witness[0]} ≢ {witness[1]} though nothing tells them"
          f" apart — unverified references are not equal by default.")

    print("\n" + "=" * 76)
    print("WHAT E31 ADDS")
    print("=" * 76)
    print("  ZTL now has FIRST-ORDER IDENTITY. It keeps the consequence")
    print("  relation of classical =: Leibniz substitutivity, symmetry and")
    print("  transitivity all hold as RULES for earned equalities (measured")
    print("  total). It loses exactly the free half — reflexivity-on-credit")
    print("  and indiscernibility-on-credit — because a verdict is never")
    print("  granted on an unverified reference. The marked individual is the")
    print("  individual-level face of Z, and it is the seed of E32 (a non-")
    print("  denoting term is a marked reference).")
    print("\n  ZEQ GREEN — identity added; free half falls on the mark, rules survive.")
