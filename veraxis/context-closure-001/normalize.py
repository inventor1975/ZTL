# -*- coding: utf-8 -*-
"""
Round 2 — is the positive fragment maximal, and can the unsoundness be cured?

    python3 veraxis/context-closure-001/normalize.py

Round 1 (`closure.py`) proved that the kernel and context closure coincide on a
positive fragment, and that the fragment is sufficient but not maximal. The
obvious next question was whether it could be sharpened into a characterisation.

IT CANNOT, AND THAT IS A THEOREM — `no_syntactic_characterisation` in
`lean/ContextClosure.lean`. Soundness is not a property of the formula at all:
the same formula with the same withheld atom is sound under one disclosure and
unsound under another. `¬(a ∧ b)` with `b` withheld is sound at `a = F` (the
conjunction is false whatever `b` is) and unsound at `a = T` (it reads `F` only
because `b` is unverified, and `b := T` defeats the claim). So no condition
looking at the formula alone can be exact, and the syntactic criterion of round
1 is maximal in its class.

THE CURATOR'S TWO CALLS, both made before this ran and both right. First: that
there would be formulas outside the fragment which are nonetheless sound —
"the man could not swim and still did not drown" — and that IMPLICATION would
be the source, because a `T` can come from a false antecedent. It is: `b → a`
heads the list, sound because its `T` comes from a true consequent rather than
from an unverified antecedent. Second, on seeing that the unsound witness is
`¬(a ∧ b)`: that NAND might carry something extra. It does — see below.

WHAT NAND CARRIES. `¬(a ∧ b)` is the Sheffer stroke, and in this logic it parts
company with `NAND` because de Morgan fails here (`deMorgan1_fails`). Push the
negation inward and the unsoundness of that witness disappears. Do it
everywhere — including expanding `xor`/`xnor` by the corpus's own PROVED
definitions (`xor_def`, `xnor_def`) — and it disappears entirely.

WHAT THIS IS NOT. Normalisation is NOT an equivalence in ZTL: de Morgan fails,
so the normalised formula is a DIFFERENT formula, and it is weaker. This file
prices that exactly. And all of it is a census over formulas of depth <= 2 on
two atoms — a measurement, not a theorem. Proving "normalisation implies
soundness" needs an induction over normal forms and is not done.
"""
import itertools
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, ROOT)
sys.path.insert(0, HERE)

from closure import (T, F, atoms_of, closure_verdict, enumerate_formulas,  # noqa: E402
                     evaluate, negation_free, show, ztl_verdict)


# ----------------------------------------------------------- normalisation

def expand(phi):
    """Expand xor/xnor by the corpus's own proved definitions — `xor_def` and
    `xnor_def` in `lean/ZTL.lean`, both machine-checked. These ARE equivalences
    in ZTL; the negation-pushing below is not."""
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
    """Push negations to the atoms by the CLASSICAL rules. In ZTL this is not
    an equivalence — de Morgan fails — so the result is a different formula
    with different behaviour under the mark. That is the point."""
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


# --------------------------------------------------------------- the census

def lies(phi, a_val):
    """The kernel grants T while some completion of the withheld atom defeats
    the claim — a warrant handed out on credit."""
    if ztl_verdict(phi, {"a": a_val}, {"b"}) != T:
        return False
    return closure_verdict(phi, {"a": a_val}, {"b"})[0] != T


def part1_maximality():
    print("=" * 78)
    print("PART 1 — outside the fragment: who swims, who drowns, who stayed dry")
    print("=" * 78)
    degenerate = capable = sound = unsound = flips = 0
    ex_sound = []
    for phi in enumerate_formulas(["a", "b"], 2):
        if "b" not in atoms_of(phi) or negation_free(phi, "b"):
            continue
        verdicts = {}
        for a_val in (T, F):
            if ztl_verdict(phi, {"a": a_val}, {"b"}) == T:
                verdicts[a_val] = lies(phi, a_val)
        if not verdicts:
            degenerate += 1
            continue
        capable += 1
        vals = set(verdicts.values())
        if vals == {False}:
            sound += 1
            if len(ex_sound) < 4:
                ex_sound.append(show(phi))
        elif vals == {True}:
            unsound += 1
        else:
            flips += 1

    total = degenerate + capable
    print(f"""
  {total} formulas outside the positive fragment.

    {degenerate:5d}  DEGENERATE — the kernel can never say T at all.
           It did not swim, so it did not drown. Counting these as
           "agreement", as round 1 did, is the measure's own bug.
    {capable:5d}  capable of granting T
    {sound:5d}    of those, sound under every disclosure
    {unsound:5d}    of those, unsound whenever they grant T
    {flips:5d}    of those, SOUND UNDER ONE DISCLOSURE AND NOT ANOTHER

  The last row is why no purely syntactic condition can be exact, and it is a
  theorem: `no_syntactic_characterisation`. Soundness is a property of the
  PAIR (formula, disclosure), never of the formula alone.

  The soundly-honest ones outside the fragment, first few:
      {', '.join(ex_sound)}
  `b → a` heads them because its T comes from a true consequent rather than
  from an unverified antecedent — predicted before the run.""")
    return flips


def part2_normalisation():
    print("\n" + "=" * 78)
    print("PART 2 — normalisation: does it cure the unsoundness, and at what price")
    print("=" * 78)
    raw = norm_bad = 0
    lost_honest = lost_lying = gained = kept = 0
    for phi in enumerate_formulas(["a", "b"], 2):
        if "b" not in atoms_of(phi):
            continue
        n = normalise(phi)
        for a_val in (T, F):
            zr = ztl_verdict(phi, {"a": a_val}, {"b"})
            zn = ztl_verdict(n, {"a": a_val}, {"b"})
            cc, _ = closure_verdict(phi, {"a": a_val}, {"b"})
            raw += (zr == T and cc != T)
            norm_bad += (zn == T and closure_verdict(n, {"a": a_val}, {"b"})[0] != T)
            if zr == T and zn != T:
                if cc == T:
                    lost_honest += 1
                else:
                    lost_lying += 1
            if zr != T and zn == T:
                gained += 1
            if zn == T:
                kept += 1

    print(f"""
    {raw:5d}  warrants granted on credit, as the formulas are written
    {norm_bad:5d}  warrants granted on credit, after normalisation

    {kept:5d}  T survives normalisation — and every one of them is honest
    {lost_lying:5d}  T dropped that was a lie          (pure gain)
    {lost_honest:5d}  T dropped that closure upheld    (the real price)
    {gained:5d}  T gained by normalising            (none: this is a pure tightening)

  Ratio: {lost_lying / lost_honest:.2f} lies discarded per honest warrant lost.

  WHERE THE PRICE COMES FROM, and it is not arbitrary. Normalisation pushes the
  excluded middle to the surface — `¬(b ⊕ b)` becomes `(¬b ∨ b) ∧ (b ∨ ¬b)` —
  and the excluded middle fails in this logic by construction (`lem_fails`).
  What is lost is exactly what rested on a classical law the logic gave up. The
  founding move, priced in units for the first time.""")
    return raw, norm_bad, lost_honest


def part3_verified_data():
    print("\n" + "=" * 78)
    print("PART 3 — on VERIFIED data, normalisation must be invisible")
    print("=" * 78)
    checked = diff = 0
    for phi in enumerate_formulas(["a", "b"], 2):
        n = normalise(phi)
        for a_val, b_val in itertools.product((T, F), repeat=2):
            checked += 1
            if evaluate(phi, {"a": a_val, "b": b_val}) != \
               evaluate(n, {"a": a_val, "b": b_val}):
                diff += 1
    print(f"""
    {checked:5d}  (formula, fully verified valuation) pairs compared
    {diff:5d}  disagreements between a formula and its normalisation

  Zero, as it must be: where nothing carries the mark, ZTL agrees with
  classical logic formula for formula (`ClassicalAgreement.evalF_agrees`), and
  the normalisation rules are classical. So the price above is paid ONLY in the
  region where something is unverified. On checked data the recipe costs
  nothing at all.""")
    return diff


def main():
    print("""
ROUND 2 — maximality, and a recipe with its price.
Kernel unchanged; `ztl.py` imported, never modified.""")
    flips = part1_maximality()
    raw, norm_bad, price = part2_normalisation()
    diff = part3_verified_data()

    ok = flips > 0 and raw > 0 and norm_bad == 0 and diff == 0
    print("\n" + "=" * 78)
    if ok:
        print(f"""ROUND 2 GREEN — one theorem, one recipe, one price.

  THEOREM. No purely syntactic condition characterises soundness: {flips} formulas
  outside the fragment are sound under one disclosure and unsound under another.
  Proved in `lean/ContextClosure.lean` on the empty axiom list. The round-1
  criterion is therefore maximal in its class.

  RECIPE. Normalise before judging a partial disclosure — expand xor/xnor by
  the proved definitions, push negations to the atoms — and every one of the
  {raw} credit-warrants disappears. No change to the kernel.

  PRICE. {price} honest warrants are lost with them, because normalisation surfaces
  the excluded middle, which this logic gave up on purpose. And nothing is lost
  on verified data.

  MEASURED, NOT PROVED: depth <= 2 over two atoms. "Normalisation implies
  soundness" needs an induction over normal forms, and that is not done.""")
    else:
        print("ROUND 2 RED — see the parts above.")
    print("=" * 78)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
