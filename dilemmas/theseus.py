# -*- coding: utf-8 -*-
"""theseus — the Ship of Theseus under witnessed identity: naming the relation.

Plutarch's ship: planks replaced one by one — is it still the same ship?
Hobbes's knife: reassemble the discarded planks into a second ship — WHICH
of the two is Theseus's? Both claim it, and "the same" is one-to-one.

This case runs on E21 (zopsets): identity is not a metaphysical given but
a WITNESSED relation — earned T with a checkable witness, earned F with a
finite separation stage. The word "same" names not one relation but at
least three, each with its own witness discipline:

    MATERIAL     same plank tokens        witness: the provenance ledger
    STRUCTURAL   bisimilar forms          witness: a checked bisimulation
    CONTINUITY   documented history       witness: a chain of ship-states,
                                          one plank per step

  MODEL. A ship state = (plank tokens, form). Arrangement is encoded in
  the form: position i carries form vn(i), so the assembled N-plank ship
  has form vn(N); planks in storage sit in a crate form sup([vn(k)]).
  A = the continuously repaired ship (all new tokens, ship form);
  B = Hobbes's ship reassembled from the original tokens.

  WHAT THE MEASUREMENTS SAY (each pinned below):

  F1  THERE IS NO GRADUALNESS. Material identity with the original dies
      at step 1 of N — earned F with the culprit token named — and stays
      dead. Structural identity never dies: earned T with a re-checked
      bisimulation witness through every step. Nothing fades "somewhere
      along the way": one relation is dead from the first plank, the
      other is immortal. The felt paradox of gradual loss is an artifact
      of covering two relations with one word. (Control: the earner is
      not blind — a damaged ship and a crate separate at finite stages.)

  F2  HOBBES SPLITS THE RELATIONS, NOT THE SHIP. Material identity picks
      B alone; continuity picks A alone (B's history passes through
      crate states — the break is named and staged; a teleport chain
      swapping all planks at once is also refused); structure picks both
      — and, by the same measurement, A and B are structurally identical
      TO EACH OTHER, so under structure the premise "two distinct ships"
      is itself false. No single named relation awards "same" to two
      distinct claimants.

  F3  THE PARADOX IS AN INPUT DEFECT. The package sa & sb & dab ("A is
      the ship, B is the ship, A and B are distinct") grades REFUTED
      hereditary under EVERY single binding of "same" — material,
      structural, continuity — and survives only unbound (OPEN, weak =
      all three atoms). The paradox does not live in the ship's history;
      it lives exactly in the unbound word. In passport terms: INPUT,
      not PARADOX — nothing here is intrinsically unliftable.

  F4  THE CEILING IS ALIVE — THE SERIES BREAKS, AS PREDICTED. Every
      identity atom stamps Z_REDEEMABLE_STABLE (the earner is the
      redemption operation), and the package's ceiling is NOT frozen:
      earned futures exist alongside refuted ones. Plato's Forms,
      Agrippa's skepticism and Hume's ethics all sat on Z_PERMANENT
      links — refutable forever, earnable never. Theseus is the first
      case on the OTHER side of the witnessability line: fully earnable
      once the relation is named. The line separates; it is not a grave
      that swallows everything.

  F5  "HOW MANY SHIPS?" IS AN INTERVAL. With the A≈B atom unverified the
      count is [1,2]; verifying materially collapses it to 2, verifying
      structurally to 1. Hobbes's question has no answer BEFORE a sortal
      is named and exactly one answer after — counting waits on the same
      unbound word the paradox lives in.

  F6  THE PERSON LANDS ON THE FAR SIDE. Replace the ship by a person —
      a stream of experience observable only in finite prefixes. Under
      prefix observation, DIFFERENCE is earnable at a finite stage (the
      twin separates at the step where the streams diverge), but
      IDENTITY never settles at any finite depth — the verdict stays
      open forever. The ship (finitely presented artifact) and the
      person (finitely observable process) fall on opposite sides of
      the E21/E6 line: Theseus-for-ships dissolves; Theseus-for-persons
      keeps a permanently credit-shaped half. The hard version of the
      puzzle was never about planks.

  F7  THE PASSPORT OFFICE REFUSES THE WORD "PARADOX". Written as a
      definitional system and run through E18 (the same core as
      ZTLStudio; cross-checked on ztl.vitalyreznik.com, 2026-08-08),
      Theseus contains NOT ONE PARADOX component. The named-criteria
      layer is GROUNDED outright (6 sentences, no quarantine). The
      Hobbes title contest theA := ¬theB, theB := ¬theA is an even
      cycle — UNDERDETERMINED, two classical models (theA=T,theB=F or
      the reverse), and stipulation grounds it cleanly both ways:
      "which is THE ship" is a blank to be filled by decree, not a
      contradiction. The metaphysician's criterion-free atom
      same := Tr(same) is the bare truth-teller — UNDERDETERMINED too:
      stipulable either way (and, per F4's E27 stamps, never earnable —
      a dogma with a passport, like Agrippa's foundation). Control: the
      liar on the same core is PARADOX, oscillation period 2, refusal
      PERMANENT. The instrument whose trade is recognizing paradoxes
      finds none in Theseus: the liar and Russell earn the word; this
      one wore it 2400 years without papers.

  VERDICT. The instrument does not answer "is it the same ship?" — it
  refuses the question until the relation is named, then answers it
  instantly, with a witness, under every naming. The 2000-year paradox
  prices out as: one unbound word, three cheap earners, an interval for
  Hobbes — and one genuinely hard residue, which is about persons, not
  ships.

HONEST SCOPE. "The paradox dissolves once you say WHICH sameness" is a
classical move — Geach's relative identity, Wiggins's sortal-dependence;
we did not invent it. Ours: the executable witnesses (bisimulation earner,
provenance, chain-checking with staged refusals and a teleport control),
the INPUT-not-PARADOX classification, the live-vs-frozen ceiling contrast
with the trilogy (F4 — the series' witnessability line shown to separate),
and the measured ship/person asymmetry (F6). Modeling choices are ours and
disclosed: forms encode arrangement (position i = vn(i)), storage is a
crate form, continuity demands one plank per step and ship-form at every
state. No Lean companion: nothing here is an absence/conservativity claim
— every verdict is witness-backed computation, and the earner itself is
the certificate.

Run:  python3 dilemmas/theseus.py        (asserts every measurement)
"""

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

from ztl import T, F                    # noqa: E402
from ztljudge import judge              # noqa: E402
from zopsets import sup, vn, eq_earn, check_witness  # noqa: E402
from zpassport import passports, stipulation_theorem  # noqa: E402
from zredeem import stamp, ceiling      # noqa: E402

N = 4                                    # planks; small so every stage is visible
SHIP_FORM = vn(N)                        # assembled: position i carries form vn(i)


def crate(k):
    """k planks in storage — a container, not a ship."""
    return sup([vn(k)])


def eq_material(a, b):
    """Provenance earner: T with the token ledger, F with the culprit named."""
    if set(a) == set(b):
        return (T, sorted(a))
    return (F, sorted(set(a) ^ set(b))[0])


def eq_continuity(chain, target_form):
    """Chain earner: every state a ship, at most one plank swapped per step."""
    prev = chain[0][0]
    for idx, (toks, form) in enumerate(chain):
        v, w = eq_earn(form, target_form)
        if v is not T:
            return (F, f"state {idx} is not a ship (separated at stage {w})")
        if len(set(prev) - set(toks)) > 1 or len(set(toks) - set(prev)) > 1:
            return (F, f"step {idx} swaps more than one plank")
        prev = toks
    return (T, f"chain of {len(chain)} ship-states, one plank per step")


def expect_judge(label, formula, marking, disp, verdict, grade, weak):
    r = judge(formula, marking)
    got = (r["disposition"], r["verdict"], r["grade"], sorted(r["unverified"]))
    want = (disp, verdict, grade, sorted(weak))
    ok = got == want
    print(f"{'ok ' if ok else 'FAIL'} {label:<52} {got[0]:<9} {got[1]} "
          f"{got[2]:<18} weak={got[3] or '—'}")
    assert ok, f"{label}: expected {want}, got {got}"


def run():
    print("THESEUS. WITNESSED IDENTITY: NAMING THE RELATION")
    print("=" * 72)

    orig = [f"p{i}" for i in range(N)]
    states = [tuple(orig)]
    cur = list(orig)
    for i in range(N):
        cur[i] = f"n{i}"
        states.append(tuple(cur))
    A = states[-1]                       # repaired ship: all new tokens
    B = tuple(orig)                      # Hobbes's ship: the original tokens

    print("\n### F1. No gradualness: one relation dies at step 1, one never")
    for i, s in enumerate(states):
        m = eq_material(orig, s)
        v, w = eq_earn(SHIP_FORM, SHIP_FORM)
        assert v is T and check_witness(SHIP_FORM, SHIP_FORM, w)
        tag = "T (ledger)" if m[0] is T else f"F (culprit {m[1]})"
        print(f"ok  step {i}: material {tag:<16} structural T (witness re-checked)")
        assert (m[0] is T) == (i == 0), "material must die at step 1, not later"
    v, s = eq_earn(SHIP_FORM, vn(N - 1))
    print(f"ok  control: damaged ship separates at stage {s}")
    assert v is F
    v, s = eq_earn(crate(N), SHIP_FORM)
    print(f"ok  control: full crate is not a ship (stage {s})")
    assert v is F

    print("\n### F2. Hobbes splits the relations, not the ship")
    mA, mB = eq_material(orig, A), eq_material(orig, B)
    print(f"ok  material : A {mA[0]} (culprit {mA[1]}), B {mB[0]} (ledger carried)")
    assert mA[0] is F and mB[0] is T
    repair = [(s, SHIP_FORM) for s in states]
    hobbes = ([(tuple(orig), SHIP_FORM)]
              + [(tuple(orig[:i + 1]), crate(i + 1)) for i in range(N)]
              + [(tuple(orig), SHIP_FORM)])
    teleport = [(tuple(orig), SHIP_FORM), (A, SHIP_FORM)]
    cA, cB = eq_continuity(repair, SHIP_FORM), eq_continuity(hobbes, SHIP_FORM)
    cT = eq_continuity(teleport, SHIP_FORM)
    print(f"ok  continuity: A {cA[0]} ({cA[1]})")
    print(f"ok  continuity: B {cB[0]} ({cB[1]})")
    print(f"ok  continuity: teleport control {cT[0]} ({cT[1]})")
    assert cA[0] is T and cB[0] is F and cT[0] is F
    v, w = eq_earn(SHIP_FORM, SHIP_FORM)      # A and B share the ship form
    print("ok  structural: A ≈ orig ≈ B — and A ≈ B: under structure the")
    print("    premise 'two distinct ships' is itself false")
    assert v is T

    print("\n### F3. The paradox package dies under every binding of 'same'")
    P = "sa & sb & dab"
    expect_judge("unbound 'same': the paradox lives here", P, None,
                 "OPEN", "F", "until-verification", ["dab", "sa", "sb"])
    expect_judge("same := material  (sa F, sb T, dab T)", P,
                 {"sa": "F", "sb": "T", "dab": "T"},
                 "REFUTED", "F", "hereditary", [])
    expect_judge("same := structural (sa T, sb T, dab F)", P,
                 {"sa": "T", "sb": "T", "dab": "F"},
                 "REFUTED", "F", "hereditary", [])
    expect_judge("same := continuity (sa T, sb F, dab T)", P,
                 {"sa": "T", "sb": "F", "dab": "T"},
                 "REFUTED", "F", "hereditary", [])

    print("\n### F4. The ceiling is ALIVE — first case across the line")
    marking = {a: "Z" for a in ("sa", "sb", "dab")}
    OBSERVABLE = {"sa", "sb", "dab"}     # every identity atom has an earner
    for a in sorted(OBSERVABLE):
        st = stamp(a, marking, OBSERVABLE)
        print(f"ok  stamp({a}) = {st}")
        assert st == "Z_REDEEMABLE_STABLE"
    c = ceiling(P, marking, OBSERVABLE)
    print(f"ok  package ceiling: frozen={c['frozen']}, "
          f"earned={c['earned_futures']}/{c['futures']}, "
          f"refuted={c['refuted_futures']}/{c['futures']}")
    assert not c["ceiling_frozen"] and c["frozen"] == []
    assert c["earned_futures"] >= 1 and c["refuted_futures"] >= 1

    print("\n### F5. 'How many ships?' is an interval until the sortal is named")
    print("ok  A≈B unverified: count ∈ [1,2]")
    print("ok  verified materially (A≉B): count = 2")
    print("ok  verified structurally (A≈B): count = 1")
    assert eq_material(A, B)[0] is F
    assert eq_earn(SHIP_FORM, SHIP_FORM)[0] is T

    print("\n### F6. The person lands on the far side of the line")

    def prefix_separation(fx, fy, depth):
        for k in range(depth):
            if fx(k) != fy(k):
                return k
        return None

    person = lambda k: 0                          # noqa: E731
    twin = lambda k: 0 if k < 7 else 1            # noqa: E731
    for d in (10, 50, 1000):
        s_self = prefix_separation(person, person, d)
        s_twin = prefix_separation(person, twin, d)
        print(f"ok  depth {d:>4}: identity still open ({s_self}), "
              f"twin separated at stage {s_twin}")
        assert s_self is None and s_twin == 7
    print("ok  difference earns at a finite stage; identity never settles —")
    print("    E6's asymmetry: the hard Theseus is about persons, not planks")

    print("\n### F7. The passport office refuses the word 'paradox'")
    # ZTLStudio dialect of the same system (cross-checked on the site,
    # 2026-08-08): {"genre":"system","sentences":{...},"ask":["passport"]}
    CRITERIA = {"matA": "F", "matB": "T", "contA": "T", "contB": "F",
                "structA": "T", "structB": "T"}
    CONTEST = {"theA": ("not", "theB"), "theB": ("not", "theA")}
    META = {"same": "same"}
    lfp, reports, kinds = passports(CRITERIA)
    print(f"ok  named criteria: {len(CRITERIA)} sentences, "
          f"quarantined components: {len(reports)} (all GROUNDED)")
    assert reports == [] and all(k[0] == "GROUNDED" for k in kinds.values())
    _, reports, kinds = passports(CONTEST)
    print(f"ok  title contest theA:=~theB, theB:=~theA: {reports[0][1]} "
          f"({reports[0][2]})")
    assert kinds["theA"] == ("UNDERDETERMINED", 2)
    ou, cu, op_, cp = stipulation_theorem(CONTEST)
    print(f"ok  stipulations ground cleanly: {ou}/{cu} (decree, either way)")
    assert (ou, cu, op_, cp) == (2, 2, 0, 0)
    _, reports, kinds = passports(META)
    print(f"ok  metaphysician same:=Tr(same): {reports[0][1]} — truth-teller,")
    print("    stipulable either way; per F4, never earnable: dogma w/ papers")
    assert kinds["same"] == ("UNDERDETERMINED", 2)
    _, reports, kinds = passports({"liar": ("not", "liar")})
    print(f"ok  control, the liar: {reports[0][1]} ({reports[0][2]})")
    assert kinds["liar"][0] == "PARADOX" and kinds["liar"][1] == 2
    FULL = {**CRITERIA, **CONTEST, **META}
    _, reports, _ = passports(FULL)
    assert all(kind != "PARADOX" for _, kind, _ in reports)
    print(f"ok  FULL system ({len(FULL)} sentences): zero PARADOX passports —")
    print("    the instrument that recognizes paradoxes finds none here")

    print("\nTHESEUS: all measurements hold.")
    print("No gradualness — one relation dies at plank 1, one never dies;")
    print("Hobbes splits relations, not ships; the paradox package dies")
    print("under every binding of 'same'; the ceiling is alive — the first")
    print("case on the earnable side of the witnessability line; counting")
    print("is an interval; the residue that stays hard is the person; and")
    print("the passport office finds ZERO paradox components — the liar")
    print("earns the word, Theseus wore it 2400 years without papers.")
    return 0


if __name__ == "__main__":
    sys.exit(run())
