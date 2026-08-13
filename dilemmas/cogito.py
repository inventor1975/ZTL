# -*- coding: utf-8 -*-
"""cogito — Descartes under warrant grades: what the doubt actually earns.

Descartes (Meditation II): "cogito, ergo sum" — the one truth said to
survive every doubt, the earned foundation of the whole edifice.  This
case disputes it — not the certainty, but its address.  Machine-checked
companion: lean/Cogito_Conservativity.lean (thinking-facts impose ZERO
obstruction on ownership: every thinking model extends with every
bearer-assignment, the witnessed occurrence intact; the subjectless world
— Lichtenberg's "es denkt" — is a model; adding the bridge premise makes
the derivation bare modus ponens; five objects, empty axiom lists).

  ATOMS.  t = "thinking is occurring" (Lichtenberg's impersonal reading);
  i = "I exist" (a subject-bearer exists); b = the BRIDGE ("all thinking
  has a bearer" — Descartes' background principle "what thinks, is",
  already a claim about subjects).

  WHAT THE MEASUREMENTS SAY (each pinned below):

  F1  NO DELIVERY WITHOUT A BRIDGE. t -> i with the thinking granted
      stays OPEN, weak link = i. Occurrence never hands the subject over.

  F2  THE LOGIC IS INNOCENT — AND DESCARTES AGREED. With the bridge in
      place the derivation is hereditary-EARNED (bare modus ponens).
      Descartes himself denied the cogito is a syllogism (Second
      Replies): he refused the bridge reading. The judge shows what that
      refusal costs: without the bridge, F1; with it, the certainty
      hangs on a premise about subjects that no doubt ever witnessed.

  F3  THE PACKAGE SHEDS LINKS AND NEVER SETTLES. ((b & t) -> i) & b & t
      & i drops weak links as grants arrive — {b,t,i} -> {b,i} -> {i} —
      and the subject itself always remains the residue: even with the
      bridge granted, "I" waits. The exact structure of Hume's ethics
      package, with the self in place of the ought.

  F4  THE PERFORMATIVE POLE — THE SERIES' UNIQUE INVERSE ATOM. t is
      witnessed by ANY mental act, including the act of doubting t:
      under the performative reading (Hintikka) the future in which t
      is refuted is operationally unreachable — every refutation
      attempt is itself an occurrence of thinking. Measured over
      reachable futures: t is EARN-ONLY — earnable futures 1, refutable
      futures 0. The mirror image of the trilogy's frozen packages
      (refutable forever, earnable never). Doubt is the one experiment
      that cannot fail — but it is an experiment about t, not about i.

  F5  THE COGITO PACKAGE LANDS IN LIMBO — a fourth settlement class.
      Under the same performative constraint the full package (with the
      subject) has NEITHER earnable NOR refutable futures: b and i are
      Z_PERMANENT (no act witnesses a bearer), so it can never be
      earned; and every refuting path runs through t = F, which the
      performance forecloses. Neither provable nor refutable, forever.
      The series map is now complete on all four poles: Forms /
      skepticism / ethics — refutable only; Theseus — fully earnable;
      "es denkt" — earnable only; "I exist" — neither.

  F6  THE SUBJECTLESS WORLD IS A MODEL. Lean: bearer_underdetermined —
      an extension where the witnessed thinking is owned and one where
      NOTHING is owned, thinking-facts identical. Third instance of the
      conservativity pattern, now a named schema: facts do not deliver
      norms (Hume), descriptions do not deliver Forms (Plato),
      occurrences do not deliver owners (Descartes). What every
      metaphysics buys, it buys with a bridge.

  F7  THE CURATOR'S EMENDATION: "SENSUS EST, ERGO EST." Three months
      before this measurement (2026-05) the curator, dissatisfied with
      Descartes on the same grounds, wrote his own version: "Sensus
      est, ergo sum" — and its grammar already does half the repair:
      the premise is IMPERSONAL ("there is sensing"), removing the "I"
      that Descartes smuggles into the premise itself with the
      first-person "cogito"; and sensus is a stronger foundation than
      cogito (doubt must be learned; pain is felt by any animal — and
      attending to a sensation is itself a sensation). Measured: the
      premise is the same earn-only diamond (F4); "ergo sum" still
      buys the bearer bridge (OPEN, weak = i) — but drop the person
      and the sentence closes: s -> e with both atoms marked by the
      ONE act that witnesses them grades EARNED hereditary with an
      EMPTY weak-link set — the only metaphysical sentence in this
      series the judge signs outright, no credit, no bridge. In Lean
      it is a theorem of the occurrence model (occurrence_exists: the
      witness itself delivers ∃): "ergo est" is free; "ergo sum" is
      forever on loan.

      THE SETTLED CANON (curator, 2026-08-08). Latin: "Sensus est,
      ergo est!" — Russian: "Смысл есть, следовательно нечто есть!"
      The Latin is honestly ambiguous THREE ways, and the judge signs
      all three: sensus = sensation (Lichtenberg's line — pain is felt
      before any reasoning); sensus est = perfect passive, "it has
      been sensed" (the most impersonal form of all); and sensus =
      MEANING (the sensus litteralis of the medieval hermeneuts — the
      curator's own reading, canonical for the Russian form): the
      semantic cogito — to doubt "there is meaning" one must MEAN
      something by the doubt, so the refutation act witnesses the
      premise; Aristotle's elenctic move in Metaphysics Γ, transposed.
      Measured below under its own atom: the meaning-reading earns
      identically, and "I" follows from meaning no more than from
      sensation — meaning carries no owner either. Rare property for
      an aphorism: usually ambiguity is where smuggling hides; here
      every branch of the ambiguity leads to an earned truth.

  VERDICT. The dispute succeeds against the address, not the feeling:
  Descartes found a genuine diamond — the only self-witnessing atom in
  philosophy, the one claim whose refutation verifies it. But the
  diamond is "thinking occurs", not "I exist". The subject arrives only
  by bridge (unwitnessable norm) or not at all; the famous certainty,
  measured, covers exactly half the sentence. Cogito stays; ergo — and sum — go.

HONEST SCOPE. The dispute's words are old: Lichtenberg's "es denkt",
Hume's unobservable self, Nietzsche, Russell ("it thinks, as it rains");
the performative reading is Hintikka (1962). Ours is the instrument: the
grade of each link, the earn-only/limbo measurement (F4/F5 — the four-pole
map is, as far as we know, new), and the machine-checked conservativity
(F6). "No act witnesses a bearer" is a stipulation of the operational
register — recorded, not proven; an introspectionist who claims direct
acquaintance with the self rejects it at the price of naming that
acquaintance as their bridge. The performative unreachability of t = F is
likewise a register stipulation, credited to Hintikka, not smuggled.

Run:  python3 dilemmas/cogito.py        (asserts every measurement)
"""

import os
import sys
from itertools import product

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

from ztljudge import judge          # noqa: E402
from zredeem import stamp, ceiling  # noqa: E402

Z = "Z"
PACKAGE = "((b & t) -> i) & b & t & i"


def expect(label, formula, marking, disp, verdict, grade, weak):
    r = judge(formula, marking)
    got = (r["disposition"], r["verdict"], r["grade"], sorted(r["unverified"]))
    want = (disp, verdict, grade, sorted(weak))
    ok = got == want
    print(f"{'ok ' if ok else 'FAIL'} {label:<56} {got[0]:<9} {got[1]} "
          f"{got[2]:<18} weak={got[3] or '—'}")
    assert ok, f"{label}: expected {want}, got {got}"


def performative_futures(formula, marking, observable):
    """Enumerate observable-atom futures, dropping t=F as operationally
    unreachable (any refutation act witnesses t) — Hintikka's performative
    reading as a reachability constraint on the future set."""
    obs = sorted(observable)
    earned = refuted = reachable = 0
    for combo in product("TF", repeat=len(obs)):
        fut = dict(zip(obs, combo))
        if fut.get("t") == "F":
            continue                      # the experiment that cannot fail
        reachable += 1
        r = judge(formula, {**marking, **fut})
        if r["disposition"] == "EARNED":
            earned += 1
        if r["disposition"] == "REFUTED":
            refuted += 1
    return reachable, earned, refuted


def run():
    print("COGITO. WHAT THE DOUBT ACTUALLY EARNS")
    print("=" * 72)

    print("\n### F1-F2. Where the certainty actually lives")
    expect("F1 t -> i, thinking granted: no delivery",
           "t -> i", {"t": "T"},
           "OPEN", "F", "until-verification", ["i"])
    expect("F2 bridge in place: bare modus ponens, earned",
           "((t & (t -> i)) -> i)", None,
           "EARNED", "T", "hereditary", ["i", "t"])

    print("\n### F3. The package sheds links and never settles")
    expect("   everything unverified", PACKAGE, None,
           "OPEN", "F", "until-verification", ["b", "i", "t"])
    expect("   thinking granted", PACKAGE, {"t": "T"},
           "OPEN", "F", "until-verification", ["b", "i"])
    expect("   thinking and bridge granted: the I still waits",
           PACKAGE, {"t": "T", "b": "T"},
           "OPEN", "F", "until-verification", ["i"])

    print("\n### F4. The performative pole: the earn-only atom")
    marking = {a: Z for a in ("b", "t", "i")}
    OBSERVABLE = {"t"}                   # thinking self-witnesses; b, i do not
    print(f"ok  stamp(t) = {stamp('t', marking, OBSERVABLE)}")
    print(f"ok  stamp(b) = {stamp('b', marking, OBSERVABLE)}")
    print(f"ok  stamp(i) = {stamp('i', marking, OBSERVABLE)}")
    assert stamp("t", marking, OBSERVABLE) == "Z_REDEEMABLE_STABLE"
    assert stamp("b", marking, OBSERVABLE) == "Z_PERMANENT"
    assert stamp("i", marking, OBSERVABLE) == "Z_PERMANENT"
    reach, earned, refuted = performative_futures("t", marking, OBSERVABLE)
    print(f"ok  t under performativity: {reach} reachable future(s), "
          f"earned {earned}, refuted {refuted} — EARN-ONLY")
    assert (reach, earned, refuted) == (1, 1, 0)
    print("ok  the mirror of the trilogy: refutation is the one unreachable")
    print("    future — doubting t is an occurrence of t (Hintikka)")

    print("\n### F5. The cogito package lands in limbo")
    c = ceiling(PACKAGE, marking, OBSERVABLE)
    print(f"ok  classical ceiling: frozen={c['frozen']}, "
          f"earned={c['earned_futures']}/{c['futures']}, "
          f"refuted={c['refuted_futures']}/{c['futures']}")
    assert c["ceiling_frozen"] and c["earned_futures"] == 0
    assert sorted(c["frozen"]) == ["b", "i"]
    reach, earned, refuted = performative_futures(PACKAGE, marking, OBSERVABLE)
    print(f"ok  performative futures: {reach} reachable, earned {earned}, "
          f"refuted {refuted} — LIMBO: neither earnable nor refutable")
    assert (earned, refuted) == (0, 0)
    print("ok  four poles now measured: refute-only (Forms/skeptic/ethics),")
    print("    both (Theseus), earn-only (es denkt), neither (the I)")

    print("\n### F6. The subjectless world is a model")
    print("ok  lean/Cogito_Conservativity.lean: bearer_underdetermined —")
    print("    owned and ownerless extensions of one thinking model, empty")
    print("    axiom lists; third instance of the conservativity schema:")
    print("    facts/norms (Hume), descriptions/Forms (Plato),")
    print("    occurrences/owners (Descartes)")

    print("\n### F7. The curator's emendation: Sensus est, ergo est")
    expect("   'ergo sum' reading: the person returns, the gap too",
           "s -> i", {"s": "T"},
           "OPEN", "F", "until-verification", ["i"])
    expect("   control: e not marked by its own act",
           "s -> e", {"s": "T"},
           "OPEN", "F", "until-verification", ["e"])
    expect("   'ergo est': both atoms marked by the one witnessing act",
           "s -> e", {"s": "T", "e": "T"},
           "EARNED", "T", "hereditary", [])
    expect("   the full sentence as a package",
           "s & ((s -> e) & e)", {"s": "T", "e": "T"},
           "EARNED", "T", "hereditary", [])
    mk7 = {a: Z for a in ("s", "e", "i")}
    assert stamp("s", mk7, {"s", "e"}) == "Z_REDEEMABLE_STABLE"
    assert stamp("e", mk7, {"s", "e"}) == "Z_REDEEMABLE_STABLE"
    assert stamp("i", mk7, {"s", "e"}) == "Z_PERMANENT"
    print("ok  stamps: s, e redeemable by the same act; i permanent as ever")
    print("ok  Lean occurrence_exists: 'ergo est' is a theorem of the")
    print("    occurrence model — the witness itself delivers the ∃")
    print("ok  the one metaphysical sentence the judge signs outright:")
    print("    Sensus est, ergo est (V. Reznik, 2026-05)")
    # the semantic reading (sensus = meaning), under its own atoms:
    # m = "there is meaning" — doubting it is itself a meaningful act
    expect("   semantic reading: m -> e, one meaningful act marks both",
           "m -> e", {"m": "T", "e": "T"},
           "EARNED", "T", "hereditary", [])
    expect("   semantic reading: 'ergo sum' fares no better",
           "m -> i", {"m": "T"},
           "OPEN", "F", "until-verification", ["i"])
    assert stamp("m", {"m": Z, "e": Z, "i": Z}, {"m", "e"}) == "Z_REDEEMABLE_STABLE"
    assert stamp("i", {"m": Z, "e": Z, "i": Z}, {"m", "e"}) == "Z_PERMANENT"
    print("ok  sensus-as-MEANING (Aristotle Γ, the curator's canonical")
    print("    Russian: «Смысл есть, следовательно нечто есть!») earns")
    print("    identically — and meaning carries no owner either")

    print("\nCOGITO: all measurements hold.")
    print("Doubt is the one experiment that cannot fail — about thinking.")
    print("The subject arrives by bridge or not at all; the certainty,")
    print("measured, covers half the sentence. Cogito stays; ergo — and sum — go.")
    return 0


if __name__ == "__main__":
    sys.exit(run())
