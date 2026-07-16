# -*- coding: utf-8 -*-
"""truths — "everyone has his own truth": run, refuted, steered.

Model: ONE world; each agent holds a partial view of it (his marking);
an agent's "truth" = his greedy verdicts over his view. Atoms p, q;
4 worlds x 4 views per agent; a pool of 10 formulas.

The capstone (the curator's): «У каждого своя правда и только ложь
общая» — each has his own truth, and only the lie is common.
"""
import os
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.dirname(os.path.abspath(__file__)))))
sys.path.insert(0, _ROOT)
sys.path.insert(0, os.path.join(_ROOT, "zhunt"))

from itertools import product

from ztl import T, F, Z, ev
from zhunt import judge

ATOMS = ["p", "q"]
POOL = [("or", "p", ("not", "p")), ("imp", "p", "p"), ("not", ("not", "p")),
        ("and", "p", "q"), ("or", "p", "q"), ("imp", "p", "q"),
        ("xnor", "p", "q"), ("xor", "p", "q"), "p", ("not", "q")]
WORLDS = list(product((T, F), repeat=2))
VIEWS = list(product((0, 1), repeat=2))


def mark(w, v):
    return {a: (w[i] if v[i] else Z) for i, a in enumerate(ATOMS)}


def jmark(w, v):
    return {a: ({T: "T", F: "F"}[w[i]] if v[i] else "M")
            for i, a in enumerate(ATOMS)}


def stones():
    print("THE STONES\n")
    dis = dis_z = 0
    for w in WORLDS:
        for vA in VIEWS:
            for vB in VIEWS:
                for phi in POOL:
                    if ev(phi, mark(w, vA)) != ev(phi, mark(w, vB)):
                        dis += 1
                        dis_z += (0 in vA or 0 in vB)
    print(f"  K1 disagreements: {dis}, of them on unverified ground: {dis_z}"
          f" (bare: {dis - dis_z})")
    assert dis == dis_z

    died = kept = 0
    died_by = {}
    for w in WORLDS:
        full = mark(w, (1, 1))
        for v in VIEWS:
            if v == (1, 1):
                continue
            for phi in POOL:
                pv = ev(phi, mark(w, v))
                if pv in (T, F):
                    grade = judge(phi, jmark(w, v))[1]
                    if pv != ev(phi, full):
                        died += 1
                        died_by[grade] = died_by.get(grade, 0) + 1
                    else:
                        kept += 1
    print(f"  K2 partial classical verdicts: kept {kept}, DIED {died} "
          f"({100 * died // (died + kept)}%) — died by grade: {died_by}")
    assert died_by == {"until-verification": died}
    print("  K3 full grounding: agents' verdicts coincide by force "
          "(the table has no agent index)")
    print("\n  'one's own truth' lives only on unverified cells, rots at 44%")
    print("  per verification, and hereditary verdicts never rot — the only")
    print("  perishable stock is the credit.")


def path():
    print("THE PATH — (p→p): F → T, the map through p\n")
    rows = [ev(("imp", "p", "p"), {"p": v}) for v in (T, F, Z)]
    print(f"  p→p over T,F,Z: {rows}")
    assert rows == [T, T, F]
    print("""
  START   p = Z          p→p = F   any number of 'truths', zero identity
  STEP    by the cell's species (the triad): an external fact — VERIFY
          (the world collapses the dispute by force); a pending case —
          DECIDE; a free cell — CHOOSE TOGETHER (joint stipulation)
  FINISH  p ∈ {T,F}      p→p = T   one truth, common decision —
          and T→T = F→F = T: the earned identity is handed to BOTH
          sides, including the one whose credit burned.""")


def debunk():
    print("THE DEBUNK — where 'false = false is true' stops working\n")
    earned = ev(("xnor", "a", "b"), {"a": F, "b": F})
    credit = ev(("xnor", "a", "b"), {"a": Z, "b": Z})
    print(f"  earned lie = earned lie (F↔F)  → {earned}   honest bookkeeping")
    print(f"  credit = credit (Z↔Z)          → {credit}   not equal EVEN to "
          "each other")
    assert earned == T and credit == F
    print("\n  the slogan's savor is the F→F row — but its 'truths' are not")
    print("  even earned lies, they are credits, and the axiom Z↔Z=F denies")
    print("  them the equality. An honest thief is still a thief: the")
    print("  modifier 'own' cannot raise the warranty grade.")


if __name__ == "__main__":
    print("EVERYONE HAS HIS OWN TRUTH — through the core\n")
    stones()
    print()
    path()
    print()
    debunk()
    print()
    print("CAPSTONE: «У каждого своя правда и только ложь общая» — truths")
    print("are private because none is a truth; the one thing the disputants")
    print("share before the grounding is the counterfeit method itself.")
