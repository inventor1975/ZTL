# -*- coding: utf-8 -*-
"""plato_third_man — the Third Man under warrant grades: the calibration case.

A dispute with a KNOWN hand-computed answer (Vlastos 1954), replayed blind by
the judge. The point of the case is not a discovery about Plato — the atoms
were chosen by us and the decomposition partly lives in that choice. The point
is CALIBRATION: on material where the checking can be redone by hand, the
grades land exactly where the hand landed in 1954, and they add what the hand
did not have — the credit/earned distinction and the named weak link.

  ATOMS (propositional skeleton; the quantifier layer is machine-checked
  separately in lean/Plato_Equality.lean, Part III, empty axiom list):

    g  things bear the character in virtue of a ground   (one-over-many)
    s  the ground is itself a further bearer             (self-predication)
    n  the ground is distinct from what it grounds       (non-identity)
    r  a further ground is owed for {things + ground}    (the regress step)
    u  one ground per character                          (uniqueness)
    q  the ground of the Ground is the Ground itself
    m  bearers RESEMBLE the ground in the character      (paradigmatism)

  TWO ARGUMENTS, NOT ONE (Parmenides 132a-b).

  The regress version (no u): the tower of Forms. MEASURED: with everything
  unverified the engine (g&s&n)->r is ON CREDIT — true only while four
  metaphysical links hold; with every premise GRANTED it is still OPEN with
  the weak link named as r. Largeness-2 is never exhibited, only demanded,
  and a finite instrument cannot exhibit an infinite ladder: r stays in
  quarantine forever, like Yablo. The regress is never EARNED and never
  REFUTED — permanently unpayable credit.

  The finite version (Vlastos): add u and no regress is needed. The bridges
  (s&n)->~q and (s&u)->q collide at depth one. MEASURED: hereditary REFUTED
  under every marking, and with s=n=u granted the weak-link list collapses
  to exactly q — the ground-identity link, the very point where U meets NI.
  Uniqueness is what turns unpayable credit into an earned contradiction:
  it cuts the tower down to one step. (In Lean: third_man, three lines.)

  THE THESIS (Plato's own negative core, and the reason this file exists):
  "that in virtue of which things bear a character cannot be a further thing
  bearing it" = s:=F. MEASURED: the engine dies hereditarily — EARNED, immune
  to whatever happens with g, n, r. So does Aristotle's exit n:=F (ground not
  separate). The judge grades both silencers EQUAL: the propositional layer
  provably does not distinguish immanentism from operationality. The
  discriminator is not here — see HONEST SCOPE below.

  THE PRICE (Parmenides 132d — Plato's own second regress). Paradigmatism
  says resemblance requires shared character: m -> s. MEASURED: (m->s)&~s&m
  is hereditary REFUTED — participation-as-resemblance dies with
  self-predication under ALL markings, not under some; and while s is merely
  unverified, m->s is OPEN with the weak link named as s: resemblance RIDES
  on self-predication. The judge points where Parmenides pointed.

HONEST SCOPE.
  * The judge settles the LOGIC layer of the 2400-year dispute: which premise
    packages are jointly tenable. It cannot pick among the consistent exits —
    that choice needs criteria outside warrant, and an instrument whose oath
    is "the verdict is authority only where warrant differs" must stay silent
    there. Not a defect; jurisdiction.
  * Every positive metaphysics of the ground sits on permanently-Z links
    (no operation witnesses s, n or u), so its ceiling is ON CREDIT; only
    refutations and vacuous silencings ever come out EARNED here. That is
    the measured shape of WHY the dispute is old: there is nothing in it to
    earn — only a choice of which credit to take.
  * The remainder of the dispute (Aristotle vs the operational reading) is
    provably invisible to this layer and to first-order content generally
    (absence of a ground-object has no formula, only a procedural trace);
    the candidate discriminator is REDEEMABILITY of the credit — a
    second-floor predicate over E24/E25 state, with SP's link provably
    Z-permanent (no act is defined over the Form). That work lives with
    ztime/zexpire/zpassport/opguard, not in this file.

Verified equivalence: the same verdicts reproduce through the full studio
pipeline (humanzfl -> zfl validator -> core), measured 2026-08-06.

Run:  python3 dilemmas/plato_third_man.py        (asserts every grade)
"""

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

from ztljudge import judge  # noqa: E402

# label, formula, marking, expected (disposition, verdict, grade, weak-links)
CASES = [
    ("regress engine, all links unverified",
     "(g & s & n) -> r", None,
     ("ON CREDIT", "T", "until-verification", ["g", "n", "r", "s"])),

    ("middle Plato: every premise granted — regress still not delivered",
     "(g & s & n) -> r", {"g": "T", "s": "T", "n": "T"},
     ("OPEN", "F", "until-verification", ["r"])),

    ("the regress step itself: demanded, never exhibited (Yablo-class)",
     "r", {"r": "Z"},
     ("OPEN", "Z", "until-verification", ["r"])),

    ("THE THESIS s=F: the engine silenced hereditarily",
     "(g & s & n) -> r", {"s": "F"},
     ("EARNED", "T", "hereditary", ["g", "n", "r"])),

    ("thesis s=F: the engine is dead permanently, not on credit",
     "~(g & s & n)", {"s": "F"},
     ("EARNED", "T", "hereditary", ["g", "n"])),

    ("Aristotle n=F: the other silencer — graded exactly equal",
     "(g & s & n) -> r", {"n": "F"},
     ("EARNED", "T", "hereditary", ["g", "r", "s"])),

    ("price: paradigmatism + thesis + resemblance — jointly impossible",
     "(m -> s) & ~s & m", None,
     ("REFUTED", "F", "hereditary", ["m", "s"])),

    ("price, drawn: no resemblance (modus tollens survives in ZTL)",
     "((m -> s) & ~s) -> ~m", None,
     ("EARNED", "T", "hereditary", ["m", "s"])),

    ("Parmenides 132d: resemblance rides on self-predication",
     "(m -> s)", {"m": "T"},
     ("OPEN", "F", "until-verification", ["s"])),

    ("Vlastos finite version: bridges + premises, all merely claimed",
     "((s & n) -> ~q) & ((s & u) -> q) & s & n & u", None,
     ("REFUTED", "F", "hereditary", ["n", "q", "s", "u"])),

    ("Vlastos finite version, premises granted: weak link collapses to q",
     "((s & n) -> ~q) & ((s & u) -> q) & s & n & u",
     {"s": "T", "n": "T", "u": "T"},
     ("REFUTED", "F", "hereditary", ["q"])),
]


def run():
    width = max(len(label) for label, *_ in CASES)
    failures = 0
    for label, formula, marking, expected in CASES:
        r = judge(formula, marking)
        got = (r["disposition"], r["verdict"], r["grade"], sorted(r["unverified"]))
        want = (expected[0], expected[1], expected[2], sorted(expected[3]))
        ok = got == want
        failures += 0 if ok else 1
        mark = "ok " if ok else "FAIL"
        print(f"{mark} {label:<{width}}  {got[0]:<9} {got[1]}  {got[2]:<18} "
              f"weak={got[3] if got[3] else '—'}")
        if not ok:
            print(f"     expected: {want}")
    print()
    if failures:
        print(f"{failures} case(s) diverged — the calibration is BROKEN")
        return 1
    print("11/11 — the judge lands where Vlastos landed by hand in 1954,")
    print("with two additions the hand did not have: the grade (unpayable")
    print("credit vs earned contradiction) and the named weak link (r for")
    print("the tower, q for the collision, s under resemblance).")
    return 0


if __name__ == "__main__":
    sys.exit(run())
