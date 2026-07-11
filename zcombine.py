# -*- coding: utf-8 -*-
"""
Expedition E13: evidence combination.

Pieces of evidence about one value = constraints; combination =
intersection. An empty intersection = an EARNED contradiction of
sources — not renormalized but exhibited. Measurements:
  1. Interval intersection; THE UNIFICATION THEOREM: verify(m, v) =
     combine(m, singleton witness [v,v]) — E12 is a special case of E13.
  2. Zadeh's paradox: Dempster's rule (conflict renormalization)
     against Smets' conjunctive rule (conflict kept in m(∅));
     ZTL verdicts on top of both.
  3. Provenance polynomials (Green–Tannen 2007, twin #6): a fact's
     pedigree = A·B + C; source retraction = zeroing a variable.
"""

from fractions import Fraction
from itertools import product

from ztl import T, F, Z

# ------------------------------------------- 1. interval evidence
def combine(iv1, iv2):
    """Intersection of constraints; None = an earned conflict."""
    lo, hi = max(iv1[0], iv2[0]), min(iv1[1], iv2[1])
    return (lo, hi) if lo <= hi else None


def verify_iv(iv, v):
    """The verification of E12 as combination with a singleton witness."""
    return combine(iv, (v, v))


def intervals():
    print("### 1. Intervals: combination = intersection; verify = a special case")
    a, b = (0, 5), (3, 9)
    print(f"  A: m∈{a};  B: m∈{b};  A⊗B: m∈{combine(a, b)} — narrowing,")
    print("  combining evidence IS the verification move (E8/E12).")
    c, d = (0, 2), (5, 9)
    r = combine(c, d)
    print(f"  A: m∈{c};  B: m∈{d};  A⊗B: {r} — EMPTY: the contradiction")
    print("  of the sources is EARNED (the verdict \"both honest\" = F, stable).")
    # the unification theorem: verify = combine with a singleton
    cases = [((0, 9), 4), ((3, 7), 5), ((0, 5), 7)]
    ok = all(verify_iv(iv, v) == combine(iv, (v, v)) for iv, v in cases)
    print(f"  Unification theorem verify=combine∘singleton: "
          f"{'✓ on all cases' if ok else '✗'}")
    print(f"  (including a failing verification: m∈(0,5), verify 7 → "
          f"{verify_iv((0, 5), 7)} — the act of checking can itself earn")
    print("  a conflict: the checker against the prior evidence)\n")


# --------------------------------------------------- 2. masses and Zadeh
def dempster(m1, m2, frame):
    """The classical Dempster rule (with conflict renormalization)."""
    raw = {}
    conflict = Fraction(0)
    for s1, w1 in m1.items():
        for s2, w2 in m2.items():
            inter = "".join(ch for ch in s1 if ch in s2)
            if inter:
                raw[inter] = raw.get(inter, Fraction(0)) + w1 * w2
            else:
                conflict += w1 * w2
    norm = 1 - conflict
    return {s: w / norm for s, w in raw.items()}, conflict


def smets(m1, m2):
    """Smets' conjunctive rule: the conflict is kept in m(∅)."""
    raw = {}
    for s1, w1 in m1.items():
        for s2, w2 in m2.items():
            inter = "".join(ch for ch in s1 if ch in s2)
            raw[inter] = raw.get(inter, Fraction(0)) + w1 * w2
    return raw


def zadeh():
    print("### 2. Zadeh's paradox: two doctors, three diagnoses (M, C, O)")
    m1 = {"M": Fraction(99, 100), "O": Fraction(1, 100)}   # doctor 1
    m2 = {"C": Fraction(99, 100), "O": Fraction(1, 100)}   # doctor 2
    print("  Doctor 1: meningitis 0.99, tumor 0.01")
    print("  Doctor 2: concussion 0.99, tumor 0.01")
    d, conf = dempster(m1, m2, "MCO")
    print(f"  DEMPSTER (renormalization): tumor = {d.get('O')} — certainty")
    print(f"  out of nowhere (both doctors nearly excluded it); the conflict "
          f"{conf} laundered.")
    s = smets(m1, m2)
    print(f"  SMETS/ZTL (conflict exhibited): m(∅) = {s.get('', 0)},"
          f" m(tumor) = {s.get('O', 0)}")
    print("  ZTL verdicts: \"tumor\" by Dempster — a stable T (FALSELY");
    print("  confident); our way — the source conflict is earned (0.9999),")
    print("  the diagnostic verdict: REFUSAL until the doctors are sorted out.")
    print("  Renormalizing conflict = laundering Z into a number — the same")
    print("  disease as the uniform prior (E9), now in combination.\n")


# ------------------------------------------- 3. provenance polynomials
def poly_eval(poly, trust):
    """poly: list of monomials (tuples of sources); trust: source→bool.
    A fact is earned ⟺ some monomial has all its sources verified."""
    return T if any(all(trust[s] for s in mono) for mono in poly) else F


def provenance():
    print("### 3. Provenance polynomials (twin #6: Green–Tannen 2007)")
    fact = [("A", "B"), ("C",)]          # the fact derivable as A·B + C
    print("  A fact with pedigree A·B + C (two independent derivations)")
    scenarios = [
        ("all sources verified", {"A": 1, "B": 1, "C": 1}),
        ("C retracted", {"A": 1, "B": 1, "C": 0}),
        ("A retracted", {"A": 0, "B": 1, "C": 1}),
        ("A and C retracted", {"A": 0, "B": 1, "C": 0}),
    ]
    for nm, trust in scenarios:
        print(f"  {nm:28s} → fact verdict: {poly_eval(fact, trust)}")
    print("  Source retraction = zeroing a variable; the fact lives while at")
    print("  least one monomial lives. Our mark pedigrees (E7) are monomials;")
    print("  evidence combination builds polynomials. The sixth twin:")
    print("  semiring provenance (Green–Tannen) — an algebra of trust in derivations.")


if __name__ == "__main__":
    print("=" * 72)
    print("E13. EVIDENCE COMBINATION: conflict is not laundered")
    print("=" * 72 + "\n")
    intervals()
    zadeh()
    provenance()
    print("\n### Summary")
    print("  Combination = intersection of constraints; verify (E12) is its")
    print("  special case (a singleton witness): the operations merged into")
    print("  one. Conflict is an earned fact, not noise for renormalization")
    print("  (Zadeh is resolved in Smets' favor). Pedigrees grew into source")
    print("  polynomials. Ignorance can be laundered neither by a prior (E9)")
    print("  nor by renormalization (E13): one principle, two chapters.")
