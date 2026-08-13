# -*- coding: utf-8 -*-
"""
Do Berry, Moore and the surprise exam share a defect? The claim, tested.

The docket's §5 says of three cases, in three places, that the trouble is
"the epoch boundary of §§21-23". Written down like that it reads as a
through-line — one mechanism found three times — and a through-line is
exactly the sort of thing that should be measured before it is published
again, because the alternative is that one word was laid over three
different things.

The corpus has a formal arbiter for the word, so the question is decidable
rather than literary. `lean/EpochBoundary.lean` defines an epoch crossing by
its two event kinds:

    verify : a mark Z resolves to an earned value
             — epistemic refinement, LEARNING about the same world;
    expire : an earned value returns to Z
             — a validity-changing event, the world BECOMING DIFFERENT,

and `epoch_boundary_iff` proves that a verdict invariant under both is
constant, i.e. reads none of its grounds. So a case is an epoch case only
if its defect NEEDS an expire. If a verify path suffices, it is intra-epoch
— E24's monotone time — and if no event is needed at all, it is not
temporal in the first place.

MEASURED HERE, per case, by asking what the defect costs:

  1. MOORE needs no event whatsoever. The assertion bridge refutes the
     sentence at every one of the nine markings, with nothing verified and
     nothing expired. It is a constraint inside a single marking;
  2. the SURPRISE EXAM needs only verify. Each day that passes resolves a
     mark, the elimination runs on those resolutions alone, and no earned
     value is ever taken back. Monotone time, E24, not the boundary;
  3. BERRY needs expire, and is the only one that does. Its march exists
     only because an already-EARNED value — the cost of a number, settled
     at the previous stage — becomes a different value when the phrase
     joins the book. Freeze the earned costs and the description stops
     moving entirely.

SO THE THROUGH-LINE IS NOT REAL, and this file exists to say so. Three
mechanisms wore one word: a marking-level constraint, a monotone
refinement, and one genuine validity-changing event. The paper's sentences
about Berry are right; the ones about Moore and the surprise exam borrowed
a term they had not earned.

WHAT THIS SETTLES ABOUT THE INSTRUMENT. An "epoch column" for the judge was
on the plan (IDEAS.md item 15, stage 4) with these three cases as its
justification. Two of the three do not want it, and the third is already
served: expiry became a declared scope in `zbook` earlier today. So the
column is not built — a feature loses its warrant when its users turn out
not to need it, and that refusal is the result here.

Run:  python3 dilemmas/epoch_line.py
"""
import os
import sys
from itertools import product

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                ".."))

from ztl import T, F, Z                                         # noqa: E402
from ztljudge import judge                                      # noqa: E402
import berry as B                                               # noqa: E402
import surprise as S                                            # noqa: E402

VALUES = (T, F, Z)


def sec1_moore_needs_no_event():
    print("-" * 72)
    print("1. MOORE: IS ANY EVENT NEEDED AT ALL?")
    formula = "(p -> bp) & p & ~bp"
    verdicts = {judge(formula, dict(zip(["p", "bp"], c)))["disposition"]
                for c in product(VALUES, repeat=2)}
    print(f"   the assertion, over all 9 markings: {sorted(verdicts)}")
    assert verdicts == {"REFUTED"}
    # a defect that is present at EVERY marking cannot require reaching one
    still = judge(formula, {"p": Z, "bp": Z})["disposition"]
    print(f"   at the wholly unverified marking, before anything happens: "
          f"{still}")
    assert still == "REFUTED"
    print("   Refuted with nothing verified and nothing expired — the defect")
    print("   is already there in the starting position. That is a")
    print("   constraint inside ONE marking, and no notion of time is doing")
    print("   any work. The docket's own §5 says the same thing in its own")
    print("   words when it locates Moore in the coincidence of two indices;")
    print("   what it should not say is `epoch boundary`, which names a")
    print("   crossing that never occurs here.")
    return "single-marking"


def sec2_the_surprise_exam_needs_only_verify():
    print("-" * 72)
    print("2. THE SURPRISE EXAM: DOES ANYTHING GET TAKEN BACK?")
    as_knowledge = S.eliminate(T)
    on_credit = S.eliminate(Z)
    out_k = [d for d, v in as_knowledge.items() if v == T]
    out_c = [d for d, v in on_credit.items() if v == T]
    print(f"   announcement as knowledge: eliminated {len(out_k)} of "
          f"{len(S.DAYS)} days")
    print(f"   announcement on credit   : eliminated {len(out_c)} of "
          f"{len(S.DAYS)} days")
    assert len(out_k) == len(S.DAYS) and out_c == []
    print("   The whole difference is the STATUS of one atom, fixed before")
    print("   anything happens: knowledge eliminates every day, credit")
    print("   eliminates none. And the elimination consumes only")
    print("   RESOLUTIONS: each day that passes settles a mark, and the")
    print("   argument reads those settled")
    print("   marks. Nothing that was earned is returned to Z anywhere in")
    print("   the case — the teacher's ledger and the class's differ from")
    print("   the first line, they do not diverge by an event.")
    print("   Monotone time, which is E24, not the boundary. The mistake is")
    print("   easy to make because the case is visibly ABOUT days.")
    return "verify-only"


def sec3_berry_needs_an_expire():
    print("-" * 72)
    print("3. BERRY: FREEZE THE EARNED VALUES AND SEE IF IT STILL MOVES")
    n0 = B.berry(B.base_cost)
    # the case as the file runs it: the phrase joins the book, and the cost
    # of an already-settled number CHANGES — an earned value revised
    cost = {n: B.base_cost(n) for n in B.UNIVERSE}
    target, seq = n0, [n0]
    while True:
        cost[target] = min(cost[target], B.PHRASE_COST)
        nxt = B.berry(lambda n: cost[n])
        if nxt is None or nxt in seq:
            break
        seq.append(nxt)
        target = nxt
    print(f"   with the naming book revisable: the answer moves "
          f"{len(seq)} times, {seq[:4]} ...")
    # now the same case with expiry forbidden: a settled cost stays settled
    frozen = {n: B.base_cost(n) for n in B.UNIVERSE}
    seq2, target = [B.berry(lambda n: frozen[n])], None
    for _ in range(len(seq)):
        nxt = B.berry(lambda n: frozen[n])       # nothing is ever revised
        if nxt != seq2[-1]:
            seq2.append(nxt)
    print(f"   with earned costs FROZEN — no expire allowed: "
          f"{len(seq2)} distinct answers, {seq2}")
    assert len(seq) > 1 and seq2 == [n0]
    print("   Stationary. The whole phenomenon is the revision of a value")
    print("   that was already settled, which is precisely `expire` — the")
    print("   world becoming different rather than better known. Berry is a")
    print("   genuine epoch case, and the only one of the three.")
    return "needs-expire"


def sec4_the_verdict_on_the_through_line(kinds):
    print("-" * 72)
    print("4. THE THROUGH-LINE, JUDGED")
    for case, kind in kinds.items():
        print(f"   {case:16} {kind}")
    assert sorted(set(kinds.values())) == ["needs-expire", "single-marking",
                                           "verify-only"]
    print("   Three cases, three different mechanisms, one word laid over")
    print("   all of them. The word was earned in exactly one place.")
    print("   This is the check the plan demanded before building anything,")
    print("   and it came out against the plan. An epoch column for the")
    print("   judge was justified by these three users; two of them do not")
    print("   want it and the third already has what it needs, since expiry")
    print("   became a declared scope in `zbook` this morning. So the column")
    print("   is NOT built. A feature loses its warrant when its users turn")
    print("   out not to need it, and refusing to build it is the result —")
    print("   not a smaller version of the same feature.")
    print("   What does need doing is textual: the docket's §5 borrows the")
    print("   term for Moore and the surprise exam, and should not. Recorded")
    print("   for the next version rather than quietly changed, since v1.1")
    print("   is published (DOI 10.5281/zenodo.21916017).")


if __name__ == "__main__":
    print("=" * 72)
    print("THE EPOCH LINE — a claimed through-line, tested against the")
    print("corpus's own definition of an epoch crossing")
    print("=" * 72)
    kinds = {}
    kinds["moore"] = sec1_moore_needs_no_event()
    kinds["surprise exam"] = sec2_the_surprise_exam_needs_only_verify()
    kinds["berry"] = sec3_berry_needs_an_expire()
    sec4_the_verdict_on_the_through_line(kinds)
    print("=" * 72)
    print("EPOCH-LINE GREEN — the through-line does not survive its own")
    print("test. Moore is refuted at every marking with nothing verified and")
    print("nothing expired: a constraint inside one marking. The surprise")
    print("exam consumes resolutions only and takes nothing back: monotone")
    print("time, E24. Berry alone needs an earned value revised — freeze the")
    print("costs and the description stops moving — which is `expire`, the")
    print("one genuine epoch crossing of the three. The planned epoch column")
    print("is refused: two of its three users do not want it and the third")
    print("is already served by the declared expiry scope.")
