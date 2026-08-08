# -*- coding: utf-8 -*-
"""hume_guillotine — Hume's law under warrant grades: the bridge, named.

Hume (Treatise III.i.1): every system of morals proceeds for a while in
is/is-not, then imperceptibly switches to ought/ought-not, and the switch is
never accounted for. No ought from is alone — the guillotine. Machine-checked
companion: lean/Hume_Guillotine.lean (descriptive axioms impose ZERO
obstruction on the ought-predicate: every descriptive model extends with
every ought-assignment, facts intact; adding a bridge premise makes the
derivation bare modus ponens — the cut lies exactly at the bridge; five
objects, empty axiom lists).

  ATOMS.  d = a descriptive fact ("the act causes suffering");
  o = the normative conclusion ("the act ought not be done");
  b = the BRIDGE ("what causes suffering ought not be done" — already a
  norm); gn = the guillotine's own commandment reading ("one ought not
  derive ought from is").

  WHAT THE MEASUREMENTS SAY (each pinned below):

  F1  NO DELIVERY WITHOUT A BRIDGE. d -> o with the fact granted stays
      OPEN, weak link = o. Description never hands the norm over.

  F2  THE LOGIC IS INNOCENT. With the bridge in place the derivation is
      hereditary-EARNED (modus ponens survives in ZTL). The guillotine
      does not cut between premise and conclusion; it cuts between
      description and norm. Blame the smuggling, not the inference.

  F3  THE JUDGE NAMES THE SMUGGLED LINK. The ethics package
      ((b & d) -> o) & b & d & o sheds weak links as facts arrive —
      {b,d,o} -> {b,o} -> {o} — and never settles: even with the bridge
      granted, the norm itself remains unwitnessed. Every ethical
      system's warrant hangs on its bridge, and the judge points at it.

  F4  THE GUILLOTINE CUTS ITSELF — AS A COMMANDMENT. Split Hume's law:
      the LOGICAL part ("no valid derivation exists") is a theorem —
      earned, machine-checked in the Lean companion. The NORMATIVE part
      ("one OUGHT NOT infer ought from is") is itself an ought: from
      facts alone it grades OPEN with weak link gn — it needs its own
      bridge, exactly like any other norm. The guillotine survives as
      theorem and dies as commandment.

  F5  ONE-DIRECTIONAL SETTLEMENT, THIRD TIME. Facts are witnessable
      (d: Z_REDEEMABLE_STABLE); bridges and norms are not (b, o:
      Z_PERMANENT under any repertoire). The ethics package's ceiling
      freezes: earned futures 0, refuted futures >= 1 — an ethics whose
      factual premise dies, dies forever; no ethics is ever earned.
      The same grave the Plato case measured for the Forms and the
      Agrippa case for global skepticism. Metaphysics, epistemology,
      ethics: three branches, one measured theorem — positive systems
      on unwitnessable links are refutable forever, earnable never.

HONEST SCOPE. The atoms are ours. F1/F2 are Hume's own points in grade
costume; the conservativity shape follows Plato_Conservativity (absence has
no formula — here: description constrains no norm). F4's self-application
is discussed in the metaethics literature (the law's own status); ours adds
the measured split theorem-vs-commandment with the link named. F5 is the
programme's through-line, structurally kin to Popper's asymmetry,
generalized to arbitrary unwitnessable warrant links. "Norms are
unwitnessable" is itself a stipulation of the operational register —
recorded, not proven; a moral realist who claims norm-perception rejects it
at the price of naming that faculty as their bridge.

Run:  python3 dilemmas/hume_guillotine.py        (asserts every measurement)
"""

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

from ztljudge import judge          # noqa: E402
from zredeem import stamp, ceiling  # noqa: E402

Z = "Z"
PACKAGE = "((b & d) -> o) & b & d & o"


def expect(label, formula, marking, disp, verdict, grade, weak):
    r = judge(formula, marking)
    got = (r["disposition"], r["verdict"], r["grade"], sorted(r["unverified"]))
    want = (disp, verdict, grade, sorted(weak))
    ok = got == want
    print(f"{'ok ' if ok else 'FAIL'} {label:<56} {got[0]:<9} {got[1]} "
          f"{got[2]:<18} weak={got[3] or '—'}")
    assert ok, f"{label}: expected {want}, got {got}"


def run():
    print("HUME. THE GUILLOTINE UNDER GRADES: THE BRIDGE, NAMED")
    print("=" * 72)

    print("\n### F1-F2. Where the cut actually lies")
    expect("F1 is -> ought, fact granted: nothing is delivered",
           "d -> o", {"d": "T"},
           "OPEN", "F", "until-verification", ["o"])
    expect("F2 bridge in place: bare modus ponens, earned",
           "((d & (d -> o)) -> o)", None,
           "EARNED", "T", "hereditary", ["d", "o"])

    print("\n### F3. The ethics package sheds links but never settles")
    expect("   everything unverified", PACKAGE, None,
           "OPEN", "F", "until-verification", ["b", "d", "o"])
    expect("   fact granted", PACKAGE, {"d": "T"},
           "OPEN", "F", "until-verification", ["b", "o"])
    expect("   fact and bridge granted: the norm still waits",
           PACKAGE, {"d": "T", "b": "T"},
           "OPEN", "F", "until-verification", ["o"])

    print("\n### F4. The guillotine as a commandment cuts itself")
    expect("   'ought not derive ought from is', from facts alone",
           "d -> gn", {"d": "T"},
           "OPEN", "F", "until-verification", ["gn"])
    print("ok  the LOGICAL part is earned elsewhere: "
          "lean/Hume_Guillotine.lean, empty axiom lists")

    print("\n### F5. Redeemability: the third one-directional settlement")
    marking = {a: Z for a in ("b", "d", "o")}
    OBSERVABLE = {"d"}            # facts are testable; bridges and norms are not
    print(f"ok  stamp(d) = {stamp('d', marking, OBSERVABLE)}")
    print(f"ok  stamp(b) = {stamp('b', marking, OBSERVABLE)}")
    print(f"ok  stamp(o) = {stamp('o', marking, OBSERVABLE)}")
    assert stamp("d", marking, OBSERVABLE) == "Z_REDEEMABLE_STABLE"
    assert stamp("b", marking, OBSERVABLE) == "Z_PERMANENT"
    assert stamp("o", marking, OBSERVABLE) == "Z_PERMANENT"
    c = ceiling(PACKAGE, marking, OBSERVABLE)
    print(f"ok  ethics package ceiling: frozen={c['frozen']}, "
          f"earned={c['earned_futures']}/{c['futures']}, "
          f"refuted={c['refuted_futures']}/{c['futures']}")
    assert c["ceiling_frozen"] and c["earned_futures"] == 0
    assert sorted(c["frozen"]) == ["b", "o"]
    assert c["refuted_futures"] >= 1

    print("\nHUME: all measurements hold.")
    print("Description delivers no norm; the logic is innocent; the judge")
    print("names the bridge; the guillotine survives as theorem and dies as")
    print("commandment; and ethics joins the Forms and the skeptic in the")
    print("same measured grave: refutable forever, earnable never.")
    return 0


if __name__ == "__main__":
    sys.exit(run())
