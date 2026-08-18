# -*- coding: utf-8 -*-
"""
The avenger's bullet, fired through the door the corpus left open.

THE QUESTION, put by the curator 2026-08-18: Tarski escaped the Liar by
defining truth for L only in L', which sends the avenger's bullet to infinity —
every device that repairs the paradox can be named and negated one level up, so
one climbs forever. Does that apply to ZTL, whose bullet is in quarantine?

THE DOOR IS REAL AND THE CORPUS NAMED IT FIRST. `lean/ZTL.lean:120` calls
`isZ_detects` "the avenger's door — the price of fork 3". The quarantine mark
IS nameable from inside: `isZ x = ¬(x↔x)`, three cells, machine-checked. So the
revenge sentence can be built, and this file builds it.

WHAT IS NOT NAMEABLE, which is half the answer:

  * `N`, the solver state under self-reference — `inductive V` has three
    constructors, T F Z, and N is not among them. A formula cannot assert "I
    am N" because there is no such value to assert.
  * the PASSPORT — GROUNDED / INTRINSIC / UNDERDETERMINED / PARADOX is computed
    by the solver over the dependency graph. It is metadata about a component,
    not a value a formula can carry, so "my passport is PARADOX" is unsayable
    for the same reason.

WHAT THE RUN SHOWS. Four constructions, and they split:

    A = isZ(A)              "my slot is unverified"     INTRINSIC, model A=F
    B = ¬isZ(B)             "my slot is verified"       INTRINSIC, model B=T
    C = isZ(C) ∨ ¬C         "unverified OR false"       PARADOX, period 2
    D = ¬isZ(D) ∧ ¬D        "verified AND false"        PARADOX, period 2

**The pure avenger does not bite.** A and B are not paradoxes but forced
stipulations: exactly one classical model each, the value compelled rather than
chosen. Saying of a slot that it is unverified does not make it verified, and
saying it is verified supplies no witness — neither statement inverts, and
inversion is what makes a liar.

**The mixed one bites, and lands where the liar already lives.** C and D pair
the register predicate with the truth predicate, and the truth half is the
ordinary liar wearing a quarantine coat. Their passport is the liar's passport:
no classical models, oscillation period 2, refusal PERMANENT.

THE ANSWER TO THE QUESTION, then. The bullet is neither dodged into an infinite
hierarchy nor caught by a new device. **It arrives in a category that already
existed.** Tarski must climb because each repair creates a liar the current
level cannot classify; here the revenge sentence is classified by the four
passports that were already there, and there is no level to climb to because
the classification is complete.

WHAT THIS DOES NOT SHOW, and the boundary matters more than the result:

  * `isZ_detects` proves the detector works on three cells. It does NOT prove
    UNIQUENESS — that no other predicate detects the mark — and the corpus says
    so itself in `inventory/conformance_package.py`. A different detector might
    behave differently under self-reference; untested.
  * Four constructions is four, not a survey. Nothing here rules out a fifth
    shape that behaves worse.
  * This is a run of the passport office, not a theorem. The Lean corpus proves
    `isZ_detects`; the classification below is computed, and computed is not
    proved.

Run:  python3 dilemmas/avenger.py
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import zpassport as zp                                          # noqa: E402


def isZ(name):
    """The quarantine detector as a formula: ¬(x ↔ x), exactly `V.isZ`."""
    return ("not", ("xnor", name, name))


SYSTEM = {
    "liar":   ("not", "liar"),                        # the classical bullet
    "truth":  "truth",                                # the truth-teller
    "A":      isZ("A"),                               # "my slot is unverified"
    "B":      ("not", isZ("B")),                      # "my slot is verified"
    "C":      ("or", isZ("C"), ("not", "C")),         # "unverified OR false"
    "D":      ("and", ("not", isZ("D")), ("not", "D")),  # "verified AND false"
}

GLOSS = {
    "liar":  "this sentence is false",
    "truth": "this sentence is true",
    "A":     "this slot is unverified",
    "B":     "this slot is verified",
    "C":     "this slot is unverified OR this sentence is false",
    "D":     "this slot is verified AND this sentence is false",
}

# KNOWN ANSWERS, written before the run and left as the assert below. A stand
# whose expectations are read off its own output proves nothing.
EXPECT = {
    "liar": "PARADOX", "truth": "UNDERDETERMINED",
    "A": "INTRINSIC", "B": "INTRINSIC",
    "C": "PARADOX", "D": "PARADOX",
}


def main():
    print("=" * 78)
    print("THE AVENGER — the revenge sentence, through the door isZ leaves open")
    print("=" * 78)

    lfp, reports, kind = zp.passports(SYSTEM)

    print(f"\n  {'name':<6} {'verdict':>8}  {'passport':<16} {'models':>7}"
          f"   what it says")
    for n in ("liar", "truth", "A", "B", "C", "D"):
        k, detail = kind[n]
        print(f"  {n:<6} {str(lfp[n]):>8}  {k:<16} {str(detail):>7}"
              f"   {GLOSS[n]}")

    for comp, k, why in sorted(reports, key=lambda r: sorted(r[0])):
        if set(comp) & {"A", "B", "C", "D"}:
            print(f"\n     {sorted(comp)}: {why}")

    bad = [n for n, want in EXPECT.items() if kind[n][0] != want]
    assert not bad, f"classification changed for {bad} — the stand is stale"

    print("""
  THE PURE AVENGER DOES NOT BITE. A and B are INTRINSIC, not paradoxical:
  exactly one classical model each, the value forced rather than chosen.
  Saying of a slot that it is unverified does not verify it; saying it is
  verified supplies no witness. Neither inverts, and inversion is what makes
  a liar.

  THE MIXED AVENGER BITES, AND LANDS WHERE THE LIAR ALREADY LIVES. C and D
  pair the register predicate with the truth predicate; the truth half is the
  ordinary liar in a quarantine coat, and it draws the liar's own passport —
  no classical models, period 2, refusal PERMANENT.

  SO THE BULLET IS NOT SENT TO INFINITY AND NOT CAUGHT BY A NEW DEVICE. It
  arrives in a category that already existed. Tarski must climb because each
  repair creates a liar the current level cannot classify; here the four
  passports classify the revenge sentence without remainder, and there is no
  level to climb to.

  Two things stay unsayable inside the language and close the second storey:
  `N` is not a constructor of `V`, and a passport is solver metadata over the
  dependency graph rather than a value a formula can carry.

  NOT PROVED HERE: uniqueness of the detector (the corpus says so itself),
  and that four shapes are a survey. This is a run, not a theorem.""")
    print("\nAVENGER STAND GREEN — the revenge sentence classifies without a "
          "new level.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
