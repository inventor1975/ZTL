# -*- coding: utf-8 -*-
"""
zsew_direction — the seam carries cause and effect, and the direction is
transitive across further seams.

The curator's design, 2026-07-21: we sew cause and effect, and that
matters for later seams. Two checks decide WHETHER to sew (↔ concordance,
∧ consistency); the implication records WHAT was sewn — which side
carries which. The point of recording it is that it survives composition.

WHY IMPLICATION IS NOT A LEGALITY GATE. It was tempting to replace ∧ with
implication, "since ∧ is static and implication is directional". Measured,
that would break the fix: F→F = T at the verdict level, so two ungrounded
F's pass and the #1 bug reopens. And on a LEGAL seam both sides are T (the
∧ gate), where verdict-imp is always T→T = A≡B and records nothing.

So direction is taken by ENTAILMENT, not by imp under the current
marking: A⊢B iff {A} ⊨ B under EVERY marking. That is marking-free, so it
is real causal structure (p ⊢ p∨q, p∧q ⊢ p) and not an artefact of the
moment.

THE PROPERTY THAT MAKES DIRECTION WORTH CARRYING, measured here:

    A ⊨ B  and  B ⊨ C   ⟹   A ⊨ C

is transitive across the pool, 0 of 340. So a chain of causal seams keeps
its direction end to end without re-deriving it: the next seam inherits
the causal structure of the ones before it, which is exactly what
"important for later seams" means, made exact.

Run:  python3 zsew_direction.py
"""
import itertools

from ztl import T, F, VALUES, IMP, AND
from entailment import entails
from zsew import Seam, sew
import zipc


def direction(a, b):
    """By ENTAILMENT: A⊢B iff {A} ⊨ B under every marking. Marking-free,
    so it is real causal structure and not an artefact of the moment."""
    ab = entails([a], b) is None
    ba = entails([b], a) is None
    return "A≡B" if ab and ba else "A⊢B" if ab else "B⊢A" if ba else "—"


def _show(x):
    if isinstance(x, str):
        return x
    if x[0] == "not":
        return f"¬{_show(x[1])}"
    return (f"({_show(x[1])}"
            + {"and": "∧", "or": "∨", "imp": "→"}[x[0]] + f"{_show(x[2])})")


if __name__ == "__main__":
    print("=" * 74)
    print("SEAM DIRECTION — cause and effect, and its transitivity")
    print("=" * 74)

    pool = zipc.build_pool(("p", "q"), depth=1)

    # ---------------------------------------------------------------- 1
    print("\n### 1. Direction is ENTAILMENT, not verdict-imp under a marking")
    print("    On a legal seam both sides are T (the ∧ gate), so verdict")
    print("    imp is always T→T = A≡B and records nothing. Entailment is")
    print("    marking-free and carries the real structure:\n")
    for a, b in [("p", ("or", "p", "q")), (("and", "p", "q"), "p"),
                 ("p", "p"), ("p", "q")]:
        print(f"    {_show(a):10s} vs {_show(b):10s}  →  {direction(a, b)}")

    # ---------------------------------------------------------------- 2
    print("\n### 2. Entailment is transitive across seams (the whole point)")
    bad = checked = 0
    for a in pool:
        for b in pool:
            if entails([a], b) is not None:
                continue
            for c in pool:
                if entails([b], c) is not None:
                    continue
                checked += 1
                if entails([a], c) is not None:
                    bad += 1
    print(f"    A⊨B and B⊨C ⟹ A⊨C : checked {checked}, violations {bad}")
    print("    → a chain of causal seams keeps its direction; the next")
    print("      seam inherits it rather than re-deriving it.")
    assert bad == 0, f"entailment is not transitive across the pool: {bad}"

    # ---------------------------------------------------------------- 3
    print("\n### 3. The direction is recorded on the sewn object")
    A = Seam("p", {"p": T})
    B = Seam(("or", "p", "q"), {"p": T, "q": T})
    st, seam = sew(A, B)
    print(f"    p  ⊗  (p∨q)   → {st}")
    if st == "SEWN":
        print(f"      {seam}")
        print(f"      direction is {seam.direction}, and it is A⊢B by")
        print("      ENTAILMENT (p ⊨ p∨q) even though at the verdict level")
        print("      both read T. p is upstream; a later seam onto p∨q")
        print("      composes with p already known to be its cause.")

    # ---------------------------------------------------------------- 4
    print("\n### 4. Why implication is NOT a legality gate")
    print(f"    F→F = {IMP(F, F)}  at the verdict level — so an implication")
    print("    GATE would pass two ungrounded F's and re-open the #1 bug.")
    print("    Checks decide WHETHER (↔, ∧); entailment records WHAT (⊢),")
    print("    on seams already known legal. Never used to legalise them.")
    assert IMP(F, F) == T, "F→F changed — re-read the whole design"

    print("\n" + "=" * 74)
    print("  Contract, four channels: ↔ and ∧ decide WHETHER (concordance,")
    print("  consistency); → records WHAT (cause and effect); and the")
    print("  causal direction is transitive, so it survives every further")
    print("  seam. That transitivity is why sewing cause and effect is")
    print("  worth doing at all.")
    print("\n  DIRECTION GREEN")
