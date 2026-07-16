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
    """The curator's LAWS OF THINKING (final wording, 2026-07-16):
    Отвергни! Подумай! Реши! — the pipeline starts by taking F for
    free, so the first law is a rejection, not a choice. Verification
    is not a member — it is the general regime of the whole logic
    (until-verification). The imperative Выбирай! stays where it
    belongs: on the free self-cell p→p — the capstone of this dilemma,
    the law of the self rather than a law of thinking."""
    print("THE LAWS OF THINKING — Отвергни! Подумай! Реши!\n")
    free_no = ev(("not", "g"), {"g": Z})
    hyp = judge(("imp", ("not", "p"), "q"), {"p": "M", "q": "M"})
    mint = ev(("not", ("not", "p")), {"p": Z})
    print(f"  ¬Z = {free_no}                the denial is free — take it first")
    print("                             → Отвергни!  (reject)")
    print(f"  ¬p→q on the unverified → {hyp[0]}, {hyp[1]}, counter p:="
          f"{hyp[2]['p']}")
    print("        a hypothesis held on credit — run its consequences")
    print("        before asserting     → Подумай!   (think it through)")
    print(f"  ¬¬p  at Z → {mint}          the hedge mints T from ignorance —")
    print("        carry the case to a direct verdict → Реши!  (decide)")
    assert free_no == F
    assert hyp[:2] == ("T", "until-verification") and hyp[2] == {"p": "F"}
    assert mint == T

    red = judge(("imp", ("imp", "p", ("not", "p")), ("not", "p")), {"p": "M"})
    cog = judge(("imp", ("imp", ("not", "p"), "p"), "p"), {"p": "M"})
    dne = judge(("imp", ("not", ("not", "p")), "p"), {"p": "M"})
    print("\nTHE PIPELINE — the three laws run as the coin algorithm\n")
    print("  1. Отвергни!  take the F-coin: assume ¬p — denial is free (¬Z=F);")
    print("     the only coin whose failure stalls instead of lying")
    print("  2. Подумай!   run the consequences of the assumption — the")
    print("     hypothesis is credit until thought through")
    print("  3. Реши!      carry to a direct verdict, and mind the barrier:")
    print(f"       reductio (p→¬p)→¬p → {red[0]}, {red[1]}   a NO from collapse — free")
    print(f"       cogito (¬p→p)→p    → {cog[0]}, {cog[1]}   a YES from collapse — credit")
    print(f"       DNE ¬¬p→p          → {dne[0]}, {dne[1]}   no way back through double NO")
    assert red[:2] == ("T", "hereditary")
    assert cog[:2] == dne[:2] == ("F", "until-verification")
    print("\n  the coin earns denials wholesale; every YES is a separate")
    print("  direct purchase — grounding, witness, verification. The coin")
    print("  buys refutations; affirmations are sold only by the world.")
    print("  And the self-cell keeps its own imperative apart from the")
    print("  laws of thinking: p→p — the world will not decide you — Выбирай!")


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
