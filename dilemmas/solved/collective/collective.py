# -*- coding: utf-8 -*-
"""collective — collective guilt: "they are all like that".

The machine that kills right now, on both sides of every war: the verdict
is stamped not on a person but on a block — a nation, a faith, a party.
Oldest recorded refusals: Abraham at Sodom (Genesis 18 — grounding demanded
per individual, down to ten) and Ezekiel 18 (guilt is not inherited).

Atoms: p = the merged group-atom ("one of THEM"); a = a grounded person;
b, g1..g3 = persons whose atoms are their own (hidden to us).

The skeleton (the curator's): (p→p)→(p→p) — and its insidiousness is
worse than credit: the fallen identity, wrapped in itself, LAUNDERS into
an unfailable hereditary constant. The machine never runs p→p on the
person (it would fall at Z); it runs the wrapper on the merged atom.
"""
import os
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.dirname(os.path.abspath(__file__)))))
sys.path.insert(0, _ROOT)
sys.path.insert(0, os.path.join(_ROOT, "zhunt"))

from ztl import T, F, Z, ev, VALUES
from zhunt import judge


def wrapper():
    print("THE WRAPPER — the fallen law laundered by self-application\n")
    pp = ("imp", "p", "p")
    w = ("imp", pp, pp)
    row_pp = [ev(pp, {"p": v}) for v in VALUES]
    row_w = [ev(w, {"p": v}) for v in VALUES]
    grade = judge(w, {"p": "M"})
    print(f"  p→p         over T,F,Z: {row_pp}   falls honestly at Z")
    print(f"  (p→p)→(p→p) over T,F,Z: {row_w}   {grade[0]}, {grade[1]}")
    assert row_pp == [T, T, F] and row_w == [T, T, T]
    assert grade[:2] == ("T", "hereditary")
    print("\n  the wrapper is not even credit — it is a hereditary CONSTANT:")
    print("  it cannot fail, so it reads nothing. Truth of the frame is not")
    print("  truth about the person ('такие уж они есть' asserts no one).")


def transfer():
    print("THE TRANSFER — identity does not travel between persons\n")
    tr = ("imp", ("imp", "a", "a"), ("imp", "b", "b"))
    v = judge(tr, {"a": "T", "b": "M"})
    print(f"  (a→a)→(b→b), b unverified → {v[0]}, {v[1]}")
    assert v[:2] == ("F", "until-verification")
    print("\n  from my identity to another's — falls at once: each person's")
    print("  atom earns only on its own ground (solved/job).")


def merge():
    print("THE MERGE — 'he is one of THEM' is not earnable\n")
    same = ("xnor", "b", "p")
    v_zz = ev(same, {"b": Z, "p": Z})
    print(f"  b↔p, both unverified → {v_zz}   (the axiom Z↔Z=F)")
    assert v_zz == F
    print("\n  two unverified atoms do not even equal EACH OTHER — the greedy")
    print("  court denies the glue. The merge that feeds the wrapper is the")
    print("  forged step: a million b_i pressed into one p with no witness.")


def slide():
    print("THE SLIDE — from an earned ∃ to a stamped ∀\n")
    ex = ("or", "g1", ("or", "g2", "g3"))
    al = ("and", "g1", ("and", "g2", "g3"))
    v_ex = judge(ex, {"g1": "T", "g2": "M", "g3": "M"})
    v_al = judge(al, {"g1": "T", "g2": "M", "g3": "M"})
    print(f"  ∃ guilty (one real criminal, g1=T) → {v_ex[0]}, {v_ex[1]}")
    print(f"  ∀ guilty ('they are ALL like that') → {v_al[0]}, {v_al[1]}")
    assert v_ex[:2] == ("T", "hereditary")
    assert v_al[:2] == ("F", "until-verification")
    print("\n  the real crime is earned and never revoked; the block verdict")
    print("  is credit on every hidden atom. The machine's sleight is the")
    print("  slide from the first to the second — the mark flows down the")
    print("  bloodline, the verdict does not (E7: taint ≠ certificate).")


def construction():
    """The correct logical construction, found by running candidates:
    a group has no atom of its own — verdicts go per person, marks may
    flow to the block. And the block verdict is ASYMMETRIC by measure:
    no pile of grounded criminals earns it; one grounded righteous
    refutes it forever. Abraham bargained with exact logic: he was not
    justifying Sodom — he was refuting the ∀."""
    blk = ("and", "g1", ("and", "g2", "g3"))
    v_pile = judge(blk, {"g1": "T", "g2": "T", "g3": "M"})
    v_one = judge(blk, {"g1": "M", "g2": "F", "g3": "M"})
    v_all = judge(blk, {"g1": "T", "g2": "T", "g3": "T"})
    print("THE CONSTRUCTION — the honest block verdict is asymmetric\n")
    print(f"  2 of 3 criminals grounded, 1 hidden → {v_pile[0]}, {v_pile[1]}")
    print(f"  1 righteous grounded, rest hidden   → {v_one[0]}, {v_one[1]}")
    print(f"  every atom walked (Abraham's limit) → {v_all[0]}, {v_all[1]}")
    assert v_pile[:2] == ("F", "until-verification")
    assert v_one[:2] == ("F", "hereditary")
    assert v_all[:2] == ("T", "hereditary")
    print("\n  no number of real criminals earns the block verdict while one")
    print("  atom stays hidden; ONE grounded righteous refutes it forever —")
    print("  and the fully-walked block is no block at all, but n personal")
    print("  verdicts. Verdicts per person; marks (suspicion, the task to")
    print("  verify) may flow to the group — the verdict may not (E7).")


if __name__ == "__main__":
    print("COLLECTIVE GUILT — 'they are all like that' through the core\n")
    wrapper()
    print()
    transfer()
    print()
    merge()
    print()
    slide()
    print()
    construction()
    print()
    print("Four cells, one machine: merge the atoms without a witness, run")
    print("the unfailable wrapper on the merged block, slide the earned ∃")
    print("into the stamped ∀. Abraham's bargain is the counter-run: ground")
    print("per person, down to ten.")
