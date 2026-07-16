# -*- coding: utf-8 -*-
"""conformity — the three paths: follow them, walk with them, or walk
your own.

The self-cell: who you are, S. Everyone treats it like induction — do as
they do, go where they go. The curator's fork is ternary: за ними / с
ними / самостоятельно — and the core has an exact cell for each.

The dilemma's answer to "what do we DO with our p→p" (the identity the
world will not decide): not a theorem to prove, not an induction to
ride — a CHOICE to make. Выбирай!
"""
import os
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.dirname(os.path.abspath(__file__)))))
sys.path.insert(0, _ROOT)
sys.path.insert(0, os.path.join(_ROOT, "zhunt"))

from ztl import T, F, Z, ev
from pengine import diagnose
from zhunt import judge


def paths():
    print("THE THREE PATHS — the self-cell S under each\n")
    d1 = diagnose({"S": "A", "A": "A"})           # follow them; they follow themselves
    d2 = diagnose({"S": "A", "A": "T"})           # walk with a grounded neighbour
    d3 = diagnose({"S": "S"})                     # your own cell
    g1 = list(d1["ground"].values())
    print(f"  за ними (S:=they, they:=they) → grounds {g1} — the whole chain "
          "is empty")
    print(f"  с ними  (S:=neighbour, he=T)  → {d2['n']} solution, S="
          f"{d2['ground']['S']} — determined, but by ANOTHER'S ground")
    print(f"  сам     (S=S)                 → {d3['n']} solutions, the world's "
          f"court: {d3['ground']['S']} — the world will NOT decide")
    assert g1 == [Z, Z]
    assert d2["n"] == 1 and d2["ground"]["S"] == T
    assert d3["n"] == 2 and d3["ground"]["S"] == Z
    print("\n  following the ungrounded carries their emptiness; walking with")
    print("  the grounded gives you a value with no author of your own; your")
    print("  own cell is the one net the world refuses to decide.")


def stipulation():
    print("THE CHOICE — the only operation that fills the cell\n")
    hold_T = ev("S", {"S": T}) == T
    hold_F = ev("S", {"S": F}) == F
    liar = diagnose({"S": ("not", "S")})
    liar_T = ev(("not", "S"), {"S": T}) == T
    liar_F = ev(("not", "S"), {"S": F}) == F
    print(f"  stipulate S:=T — holds as a fixed point: {hold_T}")
    print(f"  stipulate S:=F — holds as a fixed point: {hold_F}")
    print(f"  the liar, for contrast: {liar['n']} solutions; stipulations "
          f"hold? {liar_T}/{liar_F}")
    assert hold_T and hold_F
    assert liar["n"] == 0 and not liar_T and not liar_F
    print("\n  the liar cannot be stipulated (no door — measured); the self")
    print("  CAN, and only by its bearer: what you lay down holds by itself.")
    print("  Logic licenses BOTH values equally — which one is off logic's")
    print("  axis: freedom is the two solutions, responsibility is which.")


def triad():
    """The curator's triad of imperatives (final wording, 2026-07-16):
    three credit shapes, three kinds of honest work returned to their
    owner. Verification is not a member — it is the general regime of
    the whole logic (until-verification); the triad names the BEARER's
    three works."""
    print("THE TRIAD — three cells, three imperatives\n")
    idn = [ev(("imp", "p", "p"), {"p": v}) for v in (T, F, Z)]
    hyp = judge(("imp", ("not", "p"), "q"), {"p": "M", "q": "M"})
    mint = ev(("not", ("not", "p")), {"p": Z})
    print(f"  p→p  over T,F,Z: {idn}   the world will not decide your cell")
    print("                             → Выбирай!  (choose)")
    print(f"  ¬p→q on the unverified → {hyp[0]}, {hyp[1]}, counter p:="
          f"{hyp[2]['p']}")
    print("        a hypothesis held on credit — run its consequences")
    print("        before asserting     → Думай!    (think)")
    print(f"  ¬¬p  at Z → {mint}          the hedge mints T from ignorance —")
    print("        carry the case to a direct verdict → Решай!  (decide)")
    assert idn == [T, T, F]
    assert hyp[:2] == ("T", "until-verification") and hyp[2] == {"p": "F"}
    assert mint == T
    print("\n  a free cell — choose it; an assumption — think it through; a")
    print("  pending case — decide it. Выбирай! Думай! Решай!")

    # THE PIPELINE — the triad is also ONE algorithm, in this order:
    # the coin algorithm (the curator's, with the barrier measured).
    red = judge(("imp", ("imp", "p", ("not", "p")), ("not", "p")), {"p": "M"})
    cog = judge(("imp", ("imp", ("not", "p"), "p"), "p"), {"p": "M"})
    dne = judge(("imp", ("not", ("not", "p")), "p"), {"p": "M"})
    print("\nTHE PIPELINE — the same triad run as the coin algorithm\n")
    print("  1. Выбирай!  take the F-coin: assume ¬p — denial is free (¬Z=F);")
    print("     the only coin whose failure stalls instead of lying")
    print("  2. Думай!    run the consequences of the assumption — the")
    print("     hypothesis is credit until thought through")
    print("  3. Решай!    carry to a direct verdict, and mind the barrier:")
    print(f"       reductio (p→¬p)→¬p → {red[0]}, {red[1]}   a NO from collapse — free")
    print(f"       cogito (¬p→p)→p    → {cog[0]}, {cog[1]}   a YES from collapse — credit")
    print(f"       DNE ¬¬p→p          → {dne[0]}, {dne[1]}   no way back through double NO")
    assert red[:2] == ("T", "hereditary")
    assert cog[:2] == dne[:2] == ("F", "until-verification")
    print("\n  the coin earns denials wholesale; every YES is a separate")
    print("  direct purchase — grounding, witness, verification. The coin")
    print("  buys refutations; affirmations are sold only by the world.")


if __name__ == "__main__":
    print("CONFORMITY — follow them, walk with them, or walk your own\n")
    paths()
    print()
    stipulation()
    print()
    triad()
    print()
    print("VERDICT: the self-cell is undecidable by the world and unearnable")
    print("by induction — the only correct operation on it is the bearer's")
    print("own choice, and the chosen ground holds as a fixed point. Выбирай!")
