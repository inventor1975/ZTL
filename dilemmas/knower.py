# -*- coding: utf-8 -*-
"""
The Knower paradox (Kaplan & Montague, "A Paradox Regained", 1960).

Let d say of itself "d is not known": d <-> ~K(d). Two principles that look harmless: (T) knowledge is factive,
K(d) -> d; (N) what is proved is known — so once d is PROVED, K(d). From the diagonal and (T), d follows; by (N),
K(d); with the diagonal, ~d. The liar, rebuilt from knowledge, with no truth predicate in sight.

Picked by a scout (2026-11-09, the curator: "парадоксы какие нибудь новые"), not in the corpus before. Close to
the surprise examination's "perfect knowers" (lean/Surprise.lean §6), but the paradox is not that one: no exam,
no calendar — only factivity and necessitation.

MEASURED HERE (atoms: d — the sentence; kd — "d is known"):
  1. the three together have NO designated marking of nine — the paradox is real in the logic;
  2. the diagonal with (T) alone is satisfied in exactly one marking, d = T, kd = F: d true and unknown;
  3. the step (N) needs — "d is proved from the diagonal and (T)" — is EARNED outright only where d is CLEAN
     (d = T or F with kd clean, and d = T with kd dirty); where d or kd is dirty it is EARNED IF STABLE: proved
     only on the condition that each dirty atom is one fact at all its occurrences. Necessitation turns PROOFS
     into knowledge; a proof on a condition is not a proof outright. So (N) does not fire on a self-referential d
     whose value is not ours — the corpus's standing rule (no truth on credit) blocks the step, and the
     contradiction never forms.

WHAT THIS IS NOT: news. "Restrict necessitation" is one of the standard resolutions (SEP, Epistemic Paradoxes).
What the machine adds is that the restriction did not have to be installed: it is the IF STABLE line the judge
draws anyway. Said, not hidden: reading d as a DIRTY atom (its value set by a knower, not by us) is the modelling
step; with d clean the derivation is earned and the classical contradiction stands (§1).

Run:  python3 dilemmas/knower.py
"""
import os
import sys
from itertools import product

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

from ztl import T, F, Z                                         # noqa: E402
from ztljudge import judge                                      # noqa: E402

VALUES = (T, F, Z)
DIAG = "(d <-> ~kd)"           # d says: d is not known
FACT = "(kd -> d)"             # (T) knowledge is factive
STEP = f"(({DIAG} & {FACT}) -> d)"   # what (N) needs: d proved from the diagonal and (T)
ATOMS = ["d", "kd"]


def markings():
    return [dict(zip(ATOMS, c)) for c in product(VALUES, repeat=2)]


def sec1_the_paradox():
    print("-" * 72)
    print("1. THE THREE TOGETHER: diagonal, factivity, and d known (what (N) would give)")
    n = sum(judge(f"{DIAG} & {FACT} & kd", m)["verdict"] == T for m in markings())
    print(f"   designated markings: {n} of 9")
    assert n == 0
    print("   None. The contradiction is real in the logic, as in the classical derivation.")


def sec2_diagonal_and_factivity():
    print("-" * 72)
    print("2. THE DIAGONAL WITH FACTIVITY ALONE")
    ok = [m for m in markings() if judge(f"{DIAG} & {FACT}", m)["verdict"] == T]
    print(f"   designated: {ok}")
    assert ok == [{"d": T, "kd": F}]
    print("   Exactly one: d true and not known. So d IS true — the question is whether it is PROVED.")


def sec3_necessitation_needs_a_proof():
    print("-" * 72)
    print("3. THE STEP (N) NEEDS: d proved from the diagonal and factivity")
    disp = {(m["d"], m["kd"]): judge(STEP, m)["disposition"] for m in markings()}
    for k, v in disp.items():
        print(f"   d={k[0]} kd={k[1]}: {v}")
    outright = sorted(k for k, v in disp.items() if v == "EARNED")
    cond = sorted(k for k, v in disp.items() if v == "EARNED IF STABLE")
    assert set(outright) == {(T, T), (T, F), (T, Z), (F, T), (F, F)}
    assert set(cond) == {(F, Z), (Z, T), (Z, F), (Z, Z)}
    print("   EARNED outright only where d is clean; wherever d or kd is dirty, EARNED IF STABLE —")
    print("   proved on the condition that each dirty atom is one fact at all its occurrences.")
    print("   Necessitation makes PROOFS into knowledge; a proof on a condition is not one outright.")
    print("   A self-referential d's value is set by the knower, not by us: d is dirty, and (N) has")
    print("   nothing outright to fire on. The contradiction of §1 needs that step; it never forms.")


if __name__ == "__main__":
    sec1_the_paradox()
    sec2_diagonal_and_factivity()
    sec3_necessitation_needs_a_proof()
    print("-" * 72)
    print("KNOWER: the contradiction is real (0 of 9); the step to K(d) is earned only on a clean d —")
    print("on a dirty, self-referential d it is EARNED IF STABLE, and necessitation does not fire.")
    print("KNOWER GREEN")
