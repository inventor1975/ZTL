# -*- coding: utf-8 -*-
"""
Simpson's paradox, judged: "which treatment is better?" rides on a causal premise the table does not contain.

The kidney-stone data (Charig et al., BMJ 292, 1986, as reproduced by Julious & Mullee, BMJ 309, 1994):
treatment A succeeds more often for small stones AND for large stones, yet less often overall.

THE FORMALISATION, IN WORDS FIRST:
  two readings of "A is better", both computed from the same counts:
    POOLED      compare the overall success rates;
    STRATIFIED  compare within each stone size (and weight the strata alike).
  They disagree because A was given mostly to large (harder) stones. Two things are mixed in "is A better?", and
  only one of them is a convention (corrected 2026-11-05 after an outside review: the first version declared the
  causal premise itself a convention, which it is not):
    the QUESTION   which quantity is asked for — the pooled ASSOCIATION (who did better in this hospital's records)
                   or the causal EFFECT of the treatment on a patient. That is a choice: stipulate it.
    the ANSWER     the value of the chosen quantity. The association is read off the counts (earned). The effect is a
                   fact about the world: from these observational counts it follows only under a causal model
                   (stone size drives both the choice of treatment and the outcome) — a premise that is TOLD, not
                   verified: ON CREDIT, document the model; a randomised trial would MEASURE it.
  So the cure is two-step, as the reviewer put it: stipulate what is asked, then measure (or document) its value.

MEASURED HERE: the rates exactly (fractions); A better in each stratum, worse pooled; the judge: the question
unnamed (Q = 1 for the effect, 0 for the association, a convention): "Q == 1" OPEN, "stipulate Q"; the association
asked: "D > 0" REFUTED, earned from the counts; the effect asked, the causal model only told: "D > 0" ON CREDIT,
"document D"; the effect asked, a randomised trial still to run: OPEN, "measure D".
Run:  python3 dilemmas/simpson.py
"""
import os
import sys
from fractions import Fraction as Fr

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from znumjudge import judge_sheet_claim, parse_quantities      # noqa: E402

DATA = {"A": {"small": (81, 87), "large": (192, 263)},
        "B": {"small": (234, 270), "large": (55, 80)}}


def rate(s, n):
    return Fr(s, n)


if __name__ == "__main__":
    print("-" * 72)
    print("1. BETTER IN EACH GROUP, WORSE OVERALL")
    for g in ("small", "large"):
        a, b = rate(*DATA["A"][g]), rate(*DATA["B"][g])
        assert a > b
        print(f"   {g:5s} stones: A {float(a):.3f}  B {float(b):.3f}  -> A better")
    pa = rate(sum(s for s, _ in DATA["A"].values()), sum(n for _, n in DATA["A"].values()))
    pb = rate(sum(s for s, _ in DATA["B"].values()), sum(n for _, n in DATA["B"].values()))
    assert pa < pb
    print(f"   pooled:       A {float(pa):.3f}  B {float(pb):.3f}  -> B better")
    # stratified, standardised to the whole population's mix of stone sizes
    n_small = DATA["A"]["small"][1] + DATA["B"]["small"][1]
    n_large = DATA["A"]["large"][1] + DATA["B"]["large"][1]
    w = Fr(n_small, n_small + n_large)
    sa = w * rate(*DATA["A"]["small"]) + (1 - w) * rate(*DATA["A"]["large"])
    sb = w * rate(*DATA["B"]["small"]) + (1 - w) * rate(*DATA["B"]["large"])
    assert sa > sb
    print(f"   stratified (same mix of stones): A {float(sa):.3f}  B {float(sb):.3f}  -> A better")
    print("-" * 72)
    print("2. THE JUDGE: FIRST WHAT IS ASKED (a convention), THEN ITS VALUE (a fact)")
    q = judge_sheet_claim("Q == 1", *parse_quantities("Q=[0,1] int earned:two-questions convention"))
    assert q["disposition"] == "OPEN" and q["next_check"] == ["stipulate Q"]
    print(f"   which quantity is asked (Q = 1 effect, 0 association), unnamed: {q['disposition']} {q['next_check']}")
    lo, hi = pa - pb, sa - sb
    rows = [("the association asked (read off the counts)", f"D={lo} earned:counts", "REFUTED", []),
            ("the effect asked, the causal model only told", f"D={hi} credit", "ON CREDIT", ["document D"]),
            ("the effect asked, a randomised trial to run", f"D=[{lo},{hi}] earned:two-readings", "OPEN", ["measure D"])]
    for label, sheet, disp, cure in rows:
        r = judge_sheet_claim("D > 0", *parse_quantities(sheet))
        assert r["disposition"] == disp and r["next_check"] == cure, (label, r)
        print(f"   {label:44s}: 'D > 0' {r['disposition']:9s} {cure}")
    print("-" * 72)
    print("SIMPSON: all measurements hold.")
