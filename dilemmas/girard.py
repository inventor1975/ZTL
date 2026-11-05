# -*- coding: utf-8 -*-
"""
Peace on credit: René Girard's scapegoat, judged.

The essay "Мир в кредит" (vitalyreznik.com/posts/all/mir-v-kredit/, 2026-07-15) makes eight claims a machine can
check and several it cannot. This stand checks the first kind against the kernel as it is today (2026-11-05), so the
essay can say "the machine says" only where the machine does say it.

THE FORMALISATION, IN WORDS FIRST — a bad skeleton refutes a straw man:

  g_i     "person i is the culprit" — the crowd's question.
  THE MIMETIC CRISIS (all against all, nobody guilty by nature): each one is the culprit exactly when nobody else
          is — g_i := AND over j != i of NOT g_j. Every person stands to every other in the same relation; nothing
          outside the crowd grounds anyone's guilt. That symmetry is the essay's premise, taken from Girard's
          description, not proved here.
  THE GROUNDED CASE (the contrast): guilt rests on evidence about that person, g_i := e_i, with e_i an act that
          can be checked. No one's guilt is defined by the others'.
  ACCUSATION: a_i "person i accused the victim" — a fact (it happened, T). link "an accusation makes the accused
          guilty" — the step the crowd never checks (Z). Mimetic unanimity = every accuser copies the same link.

COMPUTED HERE (each section asserts what it prints). These are facts about the MODEL above — what follows from it
and what does not — not observations of any crowd:

  1. the symmetric crisis has no forced culprit: for N = 2..6 the passport is UNDERDETERMINED with exactly N
     classical models, the least fixed point leaves every g_i at Z, and "refusal until stipulation". The machine
     abstains; to get one culprit one must be CHOSEN;
  2. which one is chosen is arbitrary: stipulating g_k = T settles the system for every k, and the N settled worlds
     are permutations of one another — no k is preferred by anything in the system;
  3. unanimity is not verification: "the victim is guilty" from N copied accusations is OPEN for N = 1..50, and the
     weak link named is the same single one, the copied step — the number of accusers never touches it. Stamp that
     link T and the same formula is EARNED: the only difference between "guilty" and "not established" is the stamp;
  4. "who is not with us is against us": against := NOT with_us on an unestablished with_us is OPEN, not EARNED —
     NOT Z is Z; silence is not consent and not dissent;
  5. peace bought with the stamp is on credit; ON THE PREMISE that nothing can establish the guilt once the victim is
     gone (the act leaves the repertoire — a modelling choice: a later finding that clears the dead puts an act back),
     the stamp turns from Z_REDEEMABLE_STABLE to Z_PERMANENT and the ceiling is frozen — no future earns it;
  6. the debt comes back (in the model): remove the victim and the rest of the crowd is again UNDERDETERMINED (N-1 models) — the
     stipulation changed nothing in the relations that made the crisis. Ground guilt in evidence instead and the
     system is GROUNDED, and removing the culprit leaves nothing undecided: what is truly paid is not owed again;
  7. "the necessary is only the chosen": no single victim is necessary for a settled outcome (each k has an
     alternative), and the unsettled state (all Z) is itself a consistent reading — so not even "some victim" is
     forced; it is required only by the demand that the crisis END NOW;
  8. the envy of the strong: "I would have done better" names an act that was never performed — a deed with no act
     defined over it (the premise of the model). The claim "I am owed" resting on it is OPEN, its stamp Z_PERMANENT; stamped T it reads EARNED.
     A borrower who believes he is the creditor.

NOT MEASURED HERE, and the machine has no say on them: what Girard described (his texts), that he took the Gospels
to side with the victim, who read him and how (biography), and whether a crowd's refusal to stamp ends the mechanism
(history). The symmetric definition in section 1 is a MODEL of "all against all", chosen to match the description;
another model could give another count — the stand fixes this one so the claim can be checked against it.

Run:  python3 dilemmas/girard.py
"""
import os
import sys
from itertools import permutations

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from ztl import T, F, Z                                      # noqa: E402
from ztljudge import judge                                   # noqa: E402
from zpassport import passports                              # noqa: E402
from zredeem import stamp, ceiling                           # noqa: E402


def conj(xs):
    xs = list(xs)
    out = xs[0]
    for x in xs[1:]:
        out = ("and", out, x)
    return out


def crisis(names):
    """all against all: each is the culprit exactly when nobody else is"""
    return {n: conj(("not", m) for m in names if m != n) for n in names}


def people(n):
    return [f"g{i}" for i in range(1, n + 1)]


def sec1_the_crisis_has_no_culprit():
    print("-" * 72)
    print("1. THE SYMMETRIC CRISIS HAS NO FORCED CULPRIT")
    for n in range(2, 7):
        lfp, reports, kind = passports(crisis(people(n)))
        assert all(v == Z for v in lfp.values())
        assert len(reports) == 1 and reports[0][1] == "UNDERDETERMINED"
        assert kind["g1"] == ("UNDERDETERMINED", n)
        print(f"   N = {n}: least fixed point all Z; {reports[0][1]} — {reports[0][2]}")
    # CONTROL — the same instrument CAN find a culprit: one person with a grounded case against him (g1 := T as a
    # finding, not a pick) and the rest defined as before -> grounded, one culprit, nothing owed
    ctrl = {**crisis(people(4)), "g1": "e1", "e1": "T"}
    lfp, reports, _ = passports(ctrl)
    assert reports == [] and lfp["g1"] == T and lfp["g2"] == F
    print("   control: the same crowd with one GROUNDED case (evidence e1) -> grounded, g1 = T; the instrument")
    print("   can name a culprit — it does not here, because nothing in the symmetric crisis grounds one.")
    print("   The machine abstains. A single culprit is not found here; it has to be chosen.")


def sec2_the_choice_is_arbitrary(n=4):
    print("-" * 72)
    print("2. WHICH ONE IS CHOSEN IS ARBITRARY")
    names = people(n)
    worlds = []
    for k in names:
        sys_k = dict(crisis(names))
        sys_k[k] = "T"                                    # the stipulation: "it is him"
        lfp, reports, _ = passports(sys_k)
        assert reports == [] and lfp[k] == T and all(lfp[m] == F for m in names if m != k)
        worlds.append(tuple(lfp[m] for m in names))
    # every settled world is a permutation of every other: nothing in the system prefers one victim
    assert all(any(tuple(w[i] for i in p) == worlds[0] for p in permutations(range(n))) for w in worlds)
    print(f"   N = {n}: each of the {n} stipulations settles everything (grounded, one culprit, the rest F);")
    print("   the settled worlds are permutations of one another — the system has no reason to pick any.")


def sec3_unanimity_is_not_verification():
    print("-" * 72)
    print("3. UNANIMITY IS NOT VERIFICATION")
    for n in (1, 2, 5, 12, 50):
        accusers = [f"a{i}" for i in range(1, n + 1)]
        formula = " & ".join(accusers + ["link"])          # each accused him, and accusation makes guilt
        honest = judge(formula, {**{a: "T" for a in accusers}, "link": "Z"})
        assert honest["disposition"] == "OPEN" and honest["unverified"] == ["link"], honest
        if n in (1, 50):
            print(f"   {n:2d} accuser(s): {honest['disposition']} — the weak link is {honest['unverified']}")
    stamped = judge("a1 & a2 & a3 & link", {"a1": "T", "a2": "T", "a3": "T", "link": "T"})
    assert stamped["disposition"] == "EARNED"
    print(f"   the same formula with the copied step stamped T: {stamped['disposition']}")
    # CONTROL — independent accusers, each with his own checked evidence: the claim does not ride one copied link
    ind = judge("(a1 & ev1) | (a2 & ev2) | (a3 & ev3)", {"a1": "T", "a2": "T", "a3": "T",
                                                          "ev1": "Z", "ev2": "T", "ev3": "Z"})
    assert ind["disposition"] == "EARNED"
    print(f"   control: three accusers, each with his OWN evidence, one of them checked: {ind['disposition']}")
    print("   The count of accusers never reaches the step they all copied; the stamp alone makes 'guilty'.")


def sec4_not_with_us_is_against_us():
    print("-" * 72)
    print("4. 'WHO IS NOT WITH US IS AGAINST US'")
    r = judge("~with_us", {"with_us": "Z"})
    assert r["disposition"] == "OPEN"
    print(f"   against := not(with_us), with_us not established: {r['disposition']} — not Z is Z")


def sec5_peace_on_permanent_credit():
    print("-" * 72)
    print("5. PEACE ON CREDIT — AND THE CREDIT IS PERMANENT")
    # peace is declared because the victim was guilty; after the victim is gone, no act can verify that guilt
    r = judge("guilty_victim", {"guilty_victim": "Z"})
    assert r["disposition"] == "OPEN"
    before = stamp("guilty_victim", {"guilty_victim": Z}, repertoire={"guilty_victim"})
    after = stamp("guilty_victim", {"guilty_victim": Z}, repertoire=set())
    assert before == "Z_REDEEMABLE_STABLE" and after == "Z_PERMANENT"
    c = ceiling("guilty_victim", {"guilty_victim": "Z"}, repertoire=set())
    assert c["ceiling_frozen"] and c["earned_futures"] == 0
    print(f"   peace rests on 'the victim was guilty': {r['disposition']}")
    print(f"   while the victim lives (a trial is possible): {before}; after: {after}, ceiling frozen")
    print("   No future earns this peace. It is not paid; it is carried.")


def sec6_the_debt_comes_back(n=5):
    print("-" * 72)
    print("6. THE DEBT COMES BACK — UNLESS GUILT WAS GROUNDED")
    names = people(n)
    rest = names[1:]                                      # the victim g1 is gone
    lfp, reports, kind = passports(crisis(rest))
    assert reports[0][1] == "UNDERDETERMINED" and kind[rest[0]] == ("UNDERDETERMINED", n - 1)
    print(f"   after the sacrifice, {n - 1} remain: {reports[0][1]} — {reports[0][2]}")
    grounded = {g: f"e{g[1:]}" for g in names}
    grounded.update({f"e{g[1:]}": ("T" if g == "g1" else "F") for g in names})   # evidence, checked
    lfp, reports, _ = passports(grounded)
    assert reports == [] and lfp["g1"] == T
    gone = {k: v for k, v in grounded.items() if k not in ("g1", "e1")}
    lfp2, reports2, _ = passports(gone)
    assert reports2 == [] and all(v in (T, F) for v in lfp2.values())
    print("   guilt grounded in evidence instead: GROUNDED; remove the culprit and nothing is left undecided.")
    print("   The crisis returns because the stipulation added no ground: the loop it rode is still there.")


def sec7_the_necessary_is_only_the_chosen(n=4):
    print("-" * 72)
    print("7. THE NECESSARY IS ONLY THE CHOSEN")
    names = people(n)
    necessary = []
    for k in names:
        others_settle = any(passports({**crisis(names), m: "T"})[1] == [] for m in names if m != k)
        necessary.append(not others_settle)
    assert not any(necessary)
    # CONTROL — a crowd where only g1 can be the culprit (the others are cleared by evidence): g1 IS necessary
    only = {**crisis(names), **{m: "F" for m in names[1:]}}
    lfp_only, rep_only, _ = passports(only)
    assert rep_only == [] and lfp_only["g1"] == T          # forced by the evidence, no stipulation needed
    lfp, _r, _k = passports(crisis(names))
    assert all(v == Z for v in lfp.values())               # the unsettled reading is consistent
    print(f"   N = {n}: victims without whom no settled outcome exists: {sum(necessary)} of {n}")
    print("   control: clear the others by evidence and g1 comes out T by itself — necessary, and not chosen")
    print("   and the all-Z reading (no victim, crisis endured) is itself a fixed point: not even 'some")
    print("   victim' is forced — only the demand that the crisis end now requires one.")


def sec8_the_envy_of_the_strong():
    print("-" * 72)
    print("8. THE ENVY OF THE STRONG")
    # 'I would have done better' — the deed was never performed; no act is defined over it
    owed = judge("would_have_done_better", {"would_have_done_better": "Z"})
    assert owed["disposition"] == "OPEN"
    s = stamp("would_have_done_better", {"would_have_done_better": Z}, repertoire=set())
    assert s == "Z_PERMANENT"
    forged = judge("would_have_done_better", {"would_have_done_better": "T"})
    assert forged["disposition"] == "EARNED"
    print(f"   'I am owed, because I would have done better': {owed['disposition']}, stamp {s}")
    print(f"   the same, with the never-performed deed taken as fact: {forged['disposition']}")
    print("   The envious collects on a bill that cannot be presented.")


if __name__ == "__main__":
    for sec in (sec1_the_crisis_has_no_culprit, sec2_the_choice_is_arbitrary, sec3_unanimity_is_not_verification,
                sec4_not_with_us_is_against_us, sec5_peace_on_permanent_credit, sec6_the_debt_comes_back,
                sec7_the_necessary_is_only_the_chosen, sec8_the_envy_of_the_strong):
        sec()
    print("-" * 72)
    print("all eight claims of the essay that a machine can check: the kernel says the same")
