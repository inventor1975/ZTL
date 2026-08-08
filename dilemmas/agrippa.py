# -*- coding: utf-8 -*-
"""agrippa — the Münchhausen trilemma under warrant grades: pricing the horns.

Agrippa's trilemma (Sextus, Modes 4/5/2; modern form Hans Albert): every
justification chain ends in one of three ways —

    (a) infinite REGRESS       every reason needs a further reason;
    (b) CIRCLE                 the chain returns into itself;
    (c) DOGMA                  the chain stops at an unjustified foundation

— and since each horn "fails", nothing is ever justified. It is the deepest
skeptical argument on record, and it is an argument about WARRANT — the
judge's home ground. This file replays it blind, horn by horn, on the
instrument's own machinery: the judge (grades), E18 (kinds of circle,
stipulation theorem), E27 (redeemability), plus one computational lemma.

  ATOMS.  k = "the claim is EARNED" (knowledge as settled warrant);
  ra/rb/rc = the chain's shape is regress/circle/dogma; j = "unfinished
  justification yields no knowledge" — the BINARY-WARRANT premise, the
  trilemma's hidden engine; bridges (j&r*)->~k carry each horn's lethality.

  WHAT THE MEASUREMENTS SAY (each pinned as an assert below):

  F1  THE SKEPTIC'S LOGIC IS EARNED. The full inference
      (bridges & j & (ra|rb|rc)) -> ~k grades hereditary-EARNED: the
      trichotomy case analysis is valid at every marking. Agrippa is
      conceded the logic — entirely.

  F2  THE LETHALITY IS NOT IN THE LOGIC. Grant everything except j:
      the package grades OPEN with the weak link named as exactly j.
      The trilemma kills only through the premise that credit is not
      warrant — binary warrant. That premise is the argument's dogma.

  F3  UNKNOWLEDGE IS NEVER DELIVERED WHOLESALE. Even with every premise
      granted, the package waits on k itself (OPEN, weak = [k]): the
      skeptic's conclusion must be exhibited per claim, never inherited.

  F4  REGRESS = CREDIT WHOSE WEAK-LINK SET GROWS. Chains of length 2/3/4:
      grade never leaves until-verification and the unverified set gains
      one link per storey — the debt is not merely unpaid, it compounds.
      And on FINITE justification bases the horn evaporates: every total
      justifier map on n nodes repeats within n steps (checked exhaustively,
      n <= 5: zero counterexamples) — regress requires an actual infinity
      of distinct justifiers. The regress horn is an AC-class credit.

  F5  CIRCLE IS NOT ONE THING. Measured through the E18 passport:
      cycles without negation and even-negation cycles are UNDERDETERMINED
      — stipulable cleanly (the stipulation theorem holds on them);
      only odd-negation cycles are PARADOX — permanently unliftable.
      "Circularity is vicious" is false as a universal: vicious is the
      PARITY, not the circle.

  F6  DOGMA CARRIES A PASSPORT. The self-supporting foundation f := f
      with a dependent p := f measures as UNDERDETERMINED with p
      DOWNSTREAM and the culprit named ['f']; both stipulations ground
      the system cleanly (2/2, stipulation theorem). Dogma inside ZTL is
      not hidden termination — it is a named, priced, provenance-tracked
      stipulation point. (f := f is the fixed point — the same
      self-grounding exit the Plato case measured.)

  F7  THE SKEPTIC RIDES UNREDEEMABLE CREDIT — ONE-DIRECTIONAL SETTLEMENT
      AGAIN. j is a norm about warrant; no operation witnesses it: under
      any repertoire j stamps Z_PERMANENT (E27). The skeptic package's
      ceiling is frozen — earned futures 0 — while it retains refuted
      futures (any single exhibited knowledge kills it hereditarily).
      Global skepticism is a positive metaphysics of warrant sitting on
      an unredeemable link: refutable forever, earnable never. The same
      asymmetry the Plato case found for the Forms.

  VERDICT. The trilemma survives — as an EARNED trichotomy. Its lethality
  does not: it rides on binary warrant, and under graded warrant the three
  "defeats" become three different priced states — regress: compounding
  unpayable credit (and an actual-infinity vessel); circle: parity-split
  passport, only odd cycles permanent; dogma: clean stipulation with named
  culprits. The instrument does not refute Agrippa; it prices him. And its
  own answer is horn (c), taken in the open: dogma with a passport.

HONEST SCOPE. The atoms are ours; j's isolation partly lives in that
choice. "EARNED = knowledge" is a stipulation about the word "knowledge" —
recorded, not proven; a skeptic may insist on binary warrant, at the price
of naming it as his own foundation (F2 makes that unavoidable). The
finite-base lemma is checked computationally here; its Lean proof is
queued. The instrument's own tables and Z-discipline are stipulations —
horn (c), disclosed.

Run:  python3 dilemmas/agrippa.py        (asserts every measurement)
"""

import os
import sys
from itertools import product

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

from ztljudge import judge          # noqa: E402
from zpassport import passports, cycle_system, stipulation_theorem  # noqa: E402
from zredeem import stamp, ceiling  # noqa: E402

Z = "Z"

SKEPTIC = "(((j & ra) -> ~k) & ((j & rb) -> ~k) & ((j & rc) -> ~k) & j & ((ra | rb) | rc)) -> ~k"
PACKAGE = "((j & rc) -> ~k) & j & rc & ~k"


def expect(label, formula, marking, disp, verdict, grade, weak):
    r = judge(formula, marking)
    got = (r["disposition"], r["verdict"], r["grade"], sorted(r["unverified"]))
    want = (disp, verdict, grade, sorted(weak))
    ok = got == want
    print(f"{'ok ' if ok else 'FAIL'} {label:<58} {got[0]:<9} {got[1]} "
          f"{got[2]:<18} weak={got[3] or '—'}")
    assert ok, f"{label}: expected {want}, got {got}"
    return r


def run():
    print("AGRIPPA. THE TRILEMMA UNDER GRADES: PRICING THE HORNS")
    print("=" * 72)

    print("\n### F1-F3. The skeptic's engine")
    expect("F1 inference itself, everything unverified", SKEPTIC, None,
           "EARNED", "T", "hereditary", ["j", "k", "ra", "rb", "rc"])
    expect("F2 everything granted EXCEPT j", PACKAGE, {"rc": "T", "k": "F"},
           "OPEN", "F", "until-verification", ["j"])
    expect("F3 premises granted, k open", PACKAGE, {"j": "T", "rc": "T"},
           "OPEN", "F", "until-verification", ["k"])
    expect("   fully granted control", PACKAGE, {"j": "T", "rc": "T", "k": "F"},
           "EARNED", "T", "hereditary", [])

    print("\n### F4. Regress: the weak-link set compounds")
    prev = None
    for n in (2, 3, 4):
        f = " & ".join(["(q1 -> p)"]
                       + [f"(q{i+1} -> q{i})" for i in range(1, n)] + ["p"])
        r = judge(f, None)
        weak = sorted(r["unverified"])
        print(f"ok  chain length {n}: {r['disposition']} weak={weak}")
        assert r["grade"] == "until-verification"
        assert prev is None or len(weak) == len(prev) + 1
        prev = weak
    total = bad = 0
    for n in range(1, 6):
        for fmap in product(range(n), repeat=n):
            seen, x = set(), 0
            for _ in range(n + 1):
                if x in seen:
                    break
                seen.add(x)
                x = fmap[x]
            else:
                bad += 1
            total += 1
    print(f"ok  finite bases: {total} total justifier maps on n<=5 nodes, "
          f"non-repeating chains: {bad}")
    assert bad == 0, "a finite chain escaped the pigeonhole"

    print("\n### F5. Circle: the passport splits the horn by parity")
    kinds_of = {}
    for pat, name in [((0,), "self-support"), ((1,), "liar"),
                      ((0, 0), "even plain"), ((1, 1), "even negated"),
                      ((1, 1, 1), "odd negated")]:
        _, _, kinds = passports(cycle_system(pat))
        kind = sorted({k for k, _ in kinds.values()})
        kinds_of[name] = kind
        print(f"ok  cycle {name:14s}: {kind}")
    assert kinds_of["self-support"] == ["UNDERDETERMINED"]
    assert kinds_of["even plain"] == ["UNDERDETERMINED"]
    assert kinds_of["even negated"] == ["UNDERDETERMINED"]
    assert kinds_of["liar"] == ["PARADOX"]
    assert kinds_of["odd negated"] == ["PARADOX"]

    print("\n### F6. Dogma: self-supporting foundation with provenance")
    system = {"p": "f", "f": "f"}
    _, reports, kinds = passports(system)
    print(f"ok  {{p := f, f := f}}: kinds={kinds}")
    assert kinds["f"][0] == "UNDERDETERMINED"
    assert kinds["p"][0] == "DOWNSTREAM"
    culprits = [d for c, k, d in reports if k == "DOWNSTREAM"][0]
    assert "'f'" in str(culprits), "the culprit must be named"
    ok_u, cnt_u, ok_p, cnt_p = stipulation_theorem(system)
    print(f"ok  stipulation theorem on the dogma system: {ok_u}/{cnt_u} "
          f"clean groundings, {ok_p}/{cnt_p} paradox decrees")
    assert (ok_u, cnt_u) == (2, 2) and cnt_p == 0

    print("\n### F7. Redeemability: the skeptic's frozen ceiling")
    marking = {a: Z for a in ("j", "rc", "k")}
    OBSERVABLE = {"rc", "k"}       # chain shape and per-claim warrant: testable
    print(f"ok  stamp(j)  = {stamp('j', marking, OBSERVABLE)}")
    print(f"ok  stamp(k)  = {stamp('k', marking, OBSERVABLE)}")
    assert stamp("j", marking, OBSERVABLE) == "Z_PERMANENT"
    assert stamp("k", marking, OBSERVABLE) == "Z_REDEEMABLE_STABLE"
    c = ceiling(PACKAGE, marking, OBSERVABLE)
    print(f"ok  skeptic package ceiling: frozen={c['frozen']}, "
          f"earned={c['earned_futures']}/{c['futures']}, "
          f"refuted={c['refuted_futures']}/{c['futures']}")
    assert c["ceiling_frozen"] and c["earned_futures"] == 0
    assert c["refuted_futures"] >= 1

    print("\nAGRIPPA: all measurements hold.")
    print("The trichotomy is earned; the lethality is credit on j — named,")
    print("permanently unredeemable, refutable by any one exhibited knowledge.")
    print("Regress compounds and needs actual infinity; circles split by")
    print("parity; dogma is a passported stipulation. The trilemma is not")
    print("refuted — it is priced. Its price list IS this instrument.")
    return 0


if __name__ == "__main__":
    sys.exit(run())
