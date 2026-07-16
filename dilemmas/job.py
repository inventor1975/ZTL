# -*- coding: utf-8 -*-
"""job — the sufferer's guilt / victim-blaming (the Book of Job).

Atoms:  j = the world repays by deeds   (the theory — unverified)
        s = he suffers                  (observed fact — T)
        g = he is guilty                (hidden — unverified)

The friends' machine, run cell by cell: the inference is honest, the fuel
is credit, and the guilty verdict is a STIPULATION that saves a dying
theory — not an observation. Job vs the friends = the lazy register vs
the greedy one. Modern name of the machine: the just-world fallacy /
victim-blaming. The book's own ending grades the parties (42:7).
"""
import os
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)
sys.path.insert(0, os.path.join(_ROOT, "zhunt"))

from ztl import T, F, Z, ev
from fixedpoint import ev_reg, LAZY
from zhunt import judge

INF = ("imp", ("and", ("imp", "j", ("imp", "s", "g")),
               ("and", "j", "s")), "g")          # ((j→(s→g)) ∧ j ∧ s) → g
THEORY = ("xnor", "s", "g")                       # s ↔ g : suffering iff guilt


def skeleton():
    print("SKELETON (judge: verdict, warranty)\n")
    cells = [
        ("friends' inference ((j→(s→g))∧j∧s)→g", INF, {"j": "M", "s": "T", "g": "M"}),
        ("fuel   j  (the world repays)         ", "j", {"j": "M"}),
        ("verdict g (he is guilty)             ", "g", {"g": "M"}),
    ]
    out = []
    for name, phi, marks in cells:
        v, grade, _, _ = judge(phi, marks)
        print(f"  {name} → {v}, {grade}")
        out.append((v, grade))
    assert out[0] == ("T", "hereditary")          # the logic is honest
    assert out[1][1] == out[2][1] == "until-verification"
    print("\n  the inference is honest; fuel and verdict are credit.")


def stamp():
    print("THE STAMP — how guilt is manufactured\n")
    dying = ev(THEORY, {"s": T, "g": Z})          # greedy court on the honest mark
    lazyv = ev_reg(THEORY, {"s": T, "g": Z}, LAZY)
    alive_T = ev(THEORY, {"s": T, "g": T})
    alive_F = ev(THEORY, {"s": T, "g": F})
    print(f"  theory s↔g, fact s=T, g honestly unverified: greedy {dying}, lazy {lazyv}")
    print(f"  stipulate g:=T → theory {alive_T};  g:=F → theory {alive_F}")
    assert dying == F and lazyv == Z and alive_T == T and alive_F == F
    print("\n  on the honest mark the theory is DYING (greedy F); the only")
    print("  stipulation that saves it is g:=T — the verdict serves the theory.")


def registers():
    print("TWO REGISTERS — the friends vs Job, on his guilt g=Z\n")
    print(f"  greedy ¬g = {ev(('not', 'g'), {'g': Z})}   (a verdict minted from ignorance)")
    print(f"  lazy   ¬g = {ev_reg(('not', 'g'), {'g': Z}, LAZY)}   (withholds under pressure)")
    assert ev(("not", "g"), {"g": Z}) == F
    assert ev_reg(("not", "g"), {"g": Z}, LAZY) == Z
    print("\n  the friends run the greedy register (a verdict NOW); Job runs the")
    print("  lazy one (Z until ground). The demanded confession is unearned")
    print("  either way — any bivalent answer about an unverified g is credit.")


def resolution():
    """The curator's reduction: the whole book is ONE formula — g→g, the
    fallen law of identity, on the guilt atom. Identity earns exactly at
    the owner's grounding, and g is grounded only in its bearer: only the
    person can rightly assess his own guilt (the F→F version — the
    innocent knowing his innocence — IS Job)."""
    pp = ("imp", "g", "g")
    cells = [
        ("g→g outside (g unverified)", pp, {"g": "M"},
         ("F", "until-verification")),
        ("g→g self, guilty   (T→T)  ", pp, {"g": "T"}, ("T", "hereditary")),
        ("g→g self, innocent (F→F)  ", pp, {"g": "F"}, ("T", "hereditary")),
        ("¬g  Job's word, own ground", ("not", "g"), {"g": "F"},
         ("T", "hereditary")),
        ("¬g  the same word, outside", ("not", "g"), {"g": "M"},
         ("F", "until-verification")),
    ]
    print("RESOLUTION — the five cells collapse into one: g→g\n")
    for name, phi, marks, want in cells:
        v, grade, _, _ = judge(phi, marks)
        print(f"  {name} → {v}, {grade}")
        assert (v, grade) == want
    print("\n  identity — the fallen law — earns exactly at the owner's")
    print("  grounding, and the guilt atom is grounded only in its bearer:")
    print("  only the person can rightly assess his own guilt. The friends")
    print("  ran g→g on someone else's atom — their whole sin in one line.")


if __name__ == "__main__":
    print("JOB — the sufferer's guilt through the core\n")
    skeleton()
    print()
    stamp()
    print()
    registers()
    print()
    resolution()
    print()
    print("THE BOOK'S OWN GRADE (quoted, not measured — Job 42:7): the holder")
    print("of Z is vindicated, the stampers of T are condemned — the text")
    print("itself grades affirmation-on-credit as the sin.")
