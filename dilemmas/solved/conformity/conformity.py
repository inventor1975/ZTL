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


if __name__ == "__main__":
    print("CONFORMITY — follow them, walk with them, or walk your own\n")
    paths()
    print()
    stipulation()
    print()
    print("VERDICT: the self-cell is undecidable by the world and unearnable")
    print("by induction — the only correct operation on it is the bearer's")
    print("own choice, and the chosen ground holds as a fixed point. Выбирай!")
