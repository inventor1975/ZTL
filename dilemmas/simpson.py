# -*- coding: utf-8 -*-
"""
Simpson's paradox, judged: "which treatment is better?" rides on a causal premise the table does not contain.

The kidney-stone data (Charig et al., BMJ 292, 1986, as reproduced by Julious & Mullee, BMJ 309, 1994):
treatment A succeeds more often for small stones AND for large stones, yet less often overall.

THE FORMALISATION, IN WORDS FIRST:
  two readings of "A is better", both computed from the same counts:
    POOLED      compare the overall success rates;
    STRATIFIED  compare within each stone size (and weight the strata alike).
  They disagree because A was given mostly to large (harder) stones. Which reading answers "is A better for a
  patient?" depends on whether stone size influences both the choice of treatment and the outcome — a causal
  premise, not in the table. Named, the verdict is earned; unnamed, it is OPEN, and the cure is to stipulate the
  causal model — or to measure: a randomised trial makes the pooled comparison the causal one.

MEASURED HERE: the rates exactly (fractions); A better in each stratum, worse pooled; the judge with the premise
unnamed (D = success difference A - B, a convention between the pooled and the stratified value): "D > 0" OPEN,
"stipulate D"; stratified stipulated: EARNED; pooled stipulated: REFUTED; a randomised trial, to be run: "measure D".
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
    print("2. THE JUDGE ON 'A IS BETTER' (D = success rate A - B)")
    lo, hi = pa - pb, sa - sb
    rows = [("the causal premise unnamed", f"D=[{lo},{hi}] earned:two-readings convention", "OPEN", ["stipulate D"]),
            ("stratified (size drives choice and outcome)", f"D={hi} earned:stratified convention", "EARNED", []),
            ("pooled (size irrelevant)", f"D={lo} earned:pooled convention", "REFUTED", []),
            ("a randomised trial, to be run", f"D=[{lo},{hi}] earned:two-readings", "OPEN", ["measure D"])]
    for label, sheet, disp, cure in rows:
        r = judge_sheet_claim("D > 0", *parse_quantities(sheet))
        assert r["disposition"] == disp and r["next_check"] == cure, (label, r)
        print(f"   {label:44s}: {r['disposition']:8s} {cure}")
    print("-" * 72)
    print("SIMPSON: all measurements hold.")
