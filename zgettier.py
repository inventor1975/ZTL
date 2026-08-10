# -*- coding: utf-8 -*-
"""
Expedition E36: the Gettier bench — knowledge as an earned verdict.

Gettier (1963): cases where a belief is justified and true, yet is not
knowledge. This bench runs the two canonical cases (the sheep in the field,
Gettier's own ten coins) through the unchanged ZTL core, on two axes:

  the warrant axis  (ztljudge.judge)   — verdict + warranty grade + disposition;
  the refusal axis  (zpassport, E18)   — the passport office: kind of refusal.

Three floors per case, every claim under an assert:

  1. THE NAIVE AGENT admits his justification as a verified ground (T).
     The judge honestly answers EARNED — the logic is not fooled, it is
     fed a poisoned marking: the fraud happens at ADMISSION, before any
     inference. (JTB's 'justified' is weaker than EARNED: a Gettier
     justification is a T admitted on a witness that testifies about a
     different atom.)
  2. THE GATED AGENT refuses provenance-insufficient T (admission gate:
     an unwitnessed T is only Z). The judge answers OPEN — knowledge is
     never claimed; the Gettier situation dissolves before it forms.
  3. THE WORLD CORRECTS. Expelling an admitted lie is not a verification
     tick but an epoch event (the timeline machinery refuses to re-verify
     ground — E_TL_GROUND); after the correction the belief is EARNED
     again — on DIFFERENT carriers.

THE MEASURED SIGNATURE (this bench's contribution): a Gettier case is a
belief whose truth is finally carried by atoms disjoint from the atoms the
original warrant rode on —

    carriers(naive marking)  ∩  carriers(world-corrected marking)  =  ∅,

with the naive marking containing an admitted T the world refutes. The
control (honest knowledge) shares the EARNED disposition but not the
signature: its carriers coincide with the world's truth-makers.

Prior art, honestly: the DIAGNOSIS is Artemov's (The Logic of Justification,
RSL 1:4, 2008, §10, Comment 10.5 — "one of two disjuncts is justified but
false, whereas the other disjunct is unjustified but true; the resulting
disjunction is both justified and true, but not really known"). His
streamlined Case I (§10.5) is byte-for-byte the shape of our sheep. This
bench is an independent corroboration in a foreign formalism (two-valued
default-deny valuation; no justification terms, no modality) — the
convergence Williamson (Phil. Studies 172, 2015) asks formal epistemology
to seek — plus what the term machinery does not carry: an admission gate,
warranty grades, epochs, and a push-button classifier.

JURISDICTION, honestly: the signature detects misattributed warrant
(classic Gettier). It does NOT detect environment-unreliability cases
(Goldman's fake barns, 1976): there the witness points at the true atom —
carriers coincide — and the failure lives in witness sufficiency relative
to an environment, which is an admission-gate question, not a carriers
question. The bench measures this limit rather than hiding it.

Run:  python3 zgettier.py
"""
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from ztljudge import judge                          # noqa: E402
from zpassport import passports                     # noqa: E402


# ------------------------------------------------------------------ carriers
def carriers(text, marking):
    """The verified atoms the disposition actually rides on: removing the
    atom (back to the mark Z) changes the disposition. This is the
    operational reading of 'which grounds hold the verdict up'."""
    base = judge(text, marking)["disposition"]
    out = []
    for a in sorted(marking):
        rest = {k: v for k, v in marking.items() if k != a}
        if judge(text, rest)["disposition"] != base:
            out.append(a)
    return out


def gettier_signature(text, naive, world):
    """True iff the case wears Gettier's signature:
       - under the naive marking the belief is EARNED (looks like knowledge);
       - the naive marking admits at least one T the world refutes;
       - under the world's marking the belief is EARNED (it IS true);
       - the two carrier sets are disjoint (truth arrived by another road).
    """
    dn = judge(text, naive)["disposition"]
    dw = judge(text, world)["disposition"]
    smuggled = any(naive[a] == "T" and world.get(a) == "F" for a in naive)
    cn, cw = set(carriers(text, naive)), set(carriers(text, world))
    return dn == "EARNED" and dw == "EARNED" and smuggled and not (cn & cw)


def report(tag, text, marking):
    r = judge(text, marking)
    c = carriers(text, marking)
    print(f"  [{tag}]")
    print(f"    {r['formula']}   marking={marking}")
    print(f"    -> {r['disposition']} (verdict {r['verdict']}, "
          f"grade {r['grade']})   carriers={c}")
    return r, c


# ===================================================================== bench
def case_sheep():
    print("-" * 72)
    print("CASE I. THE SHEEP IN THE FIELD (Chisholm's costume of Case I)")
    print("  s1 = 'what I see in the field is a sheep'   world: F (a dog)")
    print("  s2 = 'there is a sheep behind the hill'     world: T (unseen)")
    print("  belief B = s1 | s2   ('there is a sheep in the field')")
    B = "s1 | s2"
    naive, world = {"s1": "T"}, {"s1": "F", "s2": "T"}

    r1, c1 = report("floor 1: naive agent, s1 admitted as T", B, naive)
    assert r1["disposition"] == "EARNED" and r1["grade"] == "hereditary"
    assert c1 == ["s1"], c1                 # the warrant rides the false atom

    r2, _ = report("floor 2: gated agent, unwitnessed T -> Z", B, {})
    assert r2["disposition"] == "OPEN"      # knowledge never claimed

    r3, c3 = report("floor 3: world corrects (epoch): s1:=F, s2:=T", B, world)
    assert r3["disposition"] == "EARNED"
    assert c3 == ["s2"], c3                 # truth arrived by another road

    assert gettier_signature(B, naive, world)
    print("  GETTIER SIGNATURE: carriers ['s1'] vs ['s2'], intersection = [] ✓")

    # the refusal axis: no paradox anywhere — an inherited, conditional refusal
    _, _, kinds = passports({"B": ("or", "s1", "s2"), "s1": "Z", "s2": "Z"})
    assert kinds["s1"][0] == "INPUT" and kinds["s2"][0] == "INPUT"
    assert kinds["B"] == ("DOWNSTREAM", "conditional")
    _, _, k2 = passports({"B": ("or", "s1", "s2"), "s1": "F", "s2": "T"})
    assert all(k[0] == "GROUNDED" for k in k2.values())
    assert not any(k[0] == "PARADOX" for k in list(kinds.values()) + list(k2.values()))
    print("  passport axis: s1,s2=INPUT, B=DOWNSTREAM(conditional); after the")
    print("  correction all GROUNDED; zero PARADOX — Gettier is not a paradox,")
    print("  it is a conditional refusal whose culprit the naive agent smuggled past.")


def case_coins():
    print("-" * 72)
    print("CASE II. GETTIER'S OWN TEN COINS (Case I of the 1963 paper)")
    print("  jg = 'Jones will get the job'    world: F (the boss was wrong)")
    print("  jt = 'Jones has ten coins'       world: T (Smith COUNTED them)")
    print("  sg = 'Smith will get the job'    world: T (unknown to Smith)")
    print("  st = 'Smith has ten coins'       world: T (Smith never thought of it)")
    print("  belief B = (jg & jt) | (sg & st)   ('the man who will get the job")
    print("  has ten coins in his pocket')")
    B = "(jg & jt) | (sg & st)"
    naive = {"jg": "T", "jt": "T"}
    world = {"jg": "F", "jt": "T", "sg": "T", "st": "T"}

    r1, c1 = report("floor 1: naive Smith (boss's word admitted as T)", B, naive)
    assert r1["disposition"] == "EARNED"
    assert c1 == ["jg", "jt"], c1

    r2, _ = report("floor 2: gate (boss's word is not an appointment), jt stays T",
                   B, {"jt": "T"})
    assert r2["disposition"] == "OPEN"

    r3, c3 = report("floor 3: world corrects: jg:=F; sg,st verified T", B, world)
    assert r3["disposition"] == "EARNED"
    assert c3 == ["sg", "st"], c3

    assert gettier_signature(B, naive, world)
    print("  GETTIER SIGNATURE: carriers ['jg','jt'] vs ['sg','st'],"
          " intersection = [] ✓")
    print("  note: jt was HONESTLY earned (Smith counted the coins) — one true")
    print("  witness does not launder the smuggled jg; the poisoned atom was")
    print("  load-bearing.")


def case_control():
    print("-" * 72)
    print("CONTROL. HONEST KNOWLEDGE (no signature)")
    print("  the sheep is really there and really seen: world agrees with s1")
    B = "s1 | s2"
    naive, world = {"s1": "T"}, {"s1": "T"}
    r, c = report("honest agent = world", B, naive)
    assert r["disposition"] == "EARNED" and c == ["s1"]
    assert not gettier_signature(B, naive, world)   # nothing smuggled,
    print("  same EARNED — but carriers coincide with the world's truth-makers;")
    print("  the signature does not fire. EARNED alone does not separate")
    print("  knowledge from Gettier; EARNED + carrier-match does.")


def case_fake_barn_limit():
    print("-" * 72)
    print("JURISDICTION LIMIT (measured, not hidden): FAKE BARNS (1976)")
    print("  b = 'the object before me is a barn'; Henry sees a REAL barn,")
    print("  but the county is full of papier-mache facades.")
    B = "b"
    naive, world = {"b": "T"}, {"b": "T"}   # witness points at the TRUE atom
    r, c = report("Henry in fake-barn county", B, naive)
    assert r["disposition"] == "EARNED" and c == ["b"]
    assert not gettier_signature(B, naive, world)
    print("  carriers coincide -> the signature does NOT fire, although the")
    print("  epistemologists deny Henry knowledge. The fake-barn failure is not")
    print("  misattributed warrant; it is witness sufficiency relative to an")
    print("  ENVIRONMENT — an admission-gate question (is a barn-percept a")
    print("  sufficient witness HERE?), outside this bench's jurisdiction and")
    print("  stated so. Cf. Artemov's resolution via justification identity")
    print("  (RSL 2008 §4); ZTL's admission-gate reading is complementary.")


if __name__ == "__main__":
    print("=" * 72)
    print("E36: THE GETTIER BENCH — knowledge as an earned verdict")
    print("=" * 72)
    case_sheep()
    case_coins()
    case_control()
    case_fake_barn_limit()
    print("=" * 72)
    print("E36 GREEN — two Gettier cases carry the signature (disjoint")
    print("carriers, smuggled ground); the control and the fake-barn limit do")
    print("not; the passport office finds zero paradoxes: Gettier is an")
    print("admission defect, and the ancient 'justified' is the credit ZTL")
    print("refuses.")
