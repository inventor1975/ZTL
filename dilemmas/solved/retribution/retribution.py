# -*- coding: utf-8 -*-
"""retribution — "everyone will be repaid by their deserts" (karma).

The curator's scanning method: a doctrine needs checking ONLY where it
rides the fallen laws — ¬¬p, p∨¬p, p→p. This stand runs the doctrine
through exactly those three.

Atoms:  d = he deserved it   (another's soul — hidden)
        r = it was repaid    (observable; future instances open)

The doctrine's three organs, one fallen law each:
  p→p   — "desert is desert": judging ANOTHER's desert (Job's cell);
  p∨¬p  — "deserved or not": the fork stamped over an unverified soul;
  ¬¬p   — "it WILL be repaid": the future comfort minted by double
          negation from ignorance (the E12/E22 witness cell ¬¬a0).
"""
import os
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.dirname(os.path.abspath(__file__)))))
sys.path.insert(0, _ROOT)
sys.path.insert(0, os.path.join(_ROOT, "zhunt"))

from ztl import T, F, Z, ev
from fixedpoint import ev_reg, LAZY
from zchoice import stage, greedy, LAWLESS
from zhunt import judge


def law_identity():
    print("p→p — whose desert?\n")
    pp = ("imp", "d", "d")
    outside = judge(pp, {"d": "M"})
    own_t = judge(pp, {"d": "T"})
    own_f = judge(pp, {"d": "F"})
    print(f"  d→d outside (d unverified) → {outside[0]}, {outside[1]}")
    print(f"  d→d own ground (T→T, F→F) → {own_t[0]}, {own_t[1]} / "
          f"{own_f[0]}, {own_f[1]}")
    assert outside[:2] == ("F", "until-verification")
    assert own_t[:2] == own_f[:2] == ("T", "hereditary")
    print("\n  desert, like guilt (solved/job), is grounded only in its "
          "bearer:\n  'he deserved it' is credit in every mouth but his own.")


def law_lem():
    print("p∨¬p — the stamping fork\n")
    fork = judge(("or", "d", ("not", "d")), {"d": "M"})
    print(f"  d∨¬d (deserved or not)     → {fork[0]}, {fork[1]}")
    assert fork[:2] == ("F", "until-verification")
    karma = ("xnor", "r", "d")                    # the doctrine: repaid ⟺ deserved
    mis = {v: ev(karma, {"r": F, "d": v}) for v in (Z, F, T)}
    fort = {v: ev(karma, {"r": T, "d": v}) for v in (Z, T, F)}
    print(f"  doctrine r↔d at misfortune r=F: d=Z → {mis[Z]} (dying), "
          f"saved ONLY by d:=F → {mis[F]}")
    print(f"  doctrine r↔d at fortune    r=T: d=Z → {fort[Z]} (dying), "
          f"saved ONLY by d:=T → {fort[T]}")
    assert mis[Z] == F and mis[F] == T and mis[T] == F
    assert fort[Z] == F and fort[T] == T and fort[F] == F
    print("\n  both stamps serve the theory: the sick man 'earned his karma',"
          "\n  the rich man 'earned his wealth' — two stipulations, one machine"
          "\n  (Job's friends at the bedside, the prosperity gospel at the bank).")


def law_dne():
    print("¬¬p — 'it WILL be repaid': the future minted from ignorance\n")
    dnr = ("not", ("not", "a0"))                  # a0 = the repayment, still open
    g = greedy(dnr, ())                           # greedy register at stage 0
    s = stage(dnr, (), LAWLESS)                   # the stage court
    lz = ev_reg(dnr, {"a0": Z}, LAZY)
    print(f"  ¬¬(repaid), future open: greedy {g} · stage court {s} · lazy {lz}")
    assert g == T and s == Z and lz == Z
    dne = judge(("imp", ("not", ("not", "p")), "p"), {"p": "M"})
    print(f"  DNE ¬¬p→p on the unverified → {dne[0]}, {dne[1]}")
    assert dne[:2] == ("F", "until-verification")
    print("\n  the comfort 'it will be repaid' is a greedy ¬¬ over an open"
          "\n  future — T minted from ignorance where the honest court says Z"
          "\n  (the measured E22 cell: bare greedy ¬¬ over-asserts the future).")


def steer():
    """The curator's corrected aphorism — how the doctrine must be said
    so it rides no fallen law: «Всем воздастся по заслугам — и только
    хорошее, но только то, что дадут другие.»"""
    print("THE STEER — the corrected doctrine, cell by cell\n")
    pun = judge("d", {"d": "M"})              # punitive: verdict on hidden desert
    gift = judge("give", {"give": "T"})       # the gift: giver's own grounded act
    fut = stage("a0", (), LAWLESS)            # will others give? their free cell
    print(f"  punitive 'by deserts' (d hidden)  → {pun[0]}, {pun[1]}")
    print(f"  the gift (own grounded act)       → {gift[0]}, {gift[1]}")
    print(f"  'will they give' (others' future) → {fut}")
    assert pun[:2] == ("Z", "until-verification")
    assert gift[:2] == ("T", "hereditary")
    assert fut == Z
    print("\n  the punitive half is never earnable — drop it: ONLY GOOD; the")
    print("  gift asserts nothing about the hidden atom, it cannot lie — and")
    print("  it is the giver's own grounded act: earnable. Whether they give")
    print("  is their free cell — the doctrine stops promising and starts")
    print("  addressing: the free cells are ours; WE are the repayment machine.")


if __name__ == "__main__":
    print("RETRIBUTION — 'everyone will be repaid' through the three "
          "fallen laws\n")
    law_identity()
    print()
    law_lem()
    print()
    law_dne()
    print()
    steer()
    print()
    print("The doctrine rides all three fallen laws: another's desert (p→p),")
    print("the stamped fork over a soul (p∨¬p), and a future repayment minted")
    print("by double negation (¬¬p). Each organ is credit; none is earned —")
    print("and the steer-out is the curator's corrected aphorism (see steer).")
