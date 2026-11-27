# -*- coding: utf-8 -*-
"""THE CHEAPEST PLAN OF CHECKS (zplan.py, lean/ZPlan.lean, 2026-11-27). What must hold: the plan returned settles the
claim on every branch (checked from scratch by the judge); its worst cost is the least over ALL plans - compared here
with an independent listing of every plan for small claims; the set and the best case are what they say; a ground
with no cost, too many grounds and a negative cost are refused; grounds no check can settle are never asked; the
sabotage (the better branch taken for the worse) is caught. Small hand-made claims.
Run: python3 test_zplan.py"""
import itertools
import os
import random
import sys
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import zplan                                              # noqa: E402
from ztl import T, F, Z                                   # noqa: E402
from ztljudge import judge, _show, _atoms, formalize      # noqa: E402

CHECKS, FAILS = 0, []


def check(c, what, show=None):
    global CHECKS
    CHECKS += 1
    if not c:
        FAILS.append(what)
        print("FAIL:", what, "" if show is None else show)


blank = lambda claim: {a: Z for a in _atoms(formalize(claim))}

# 1. the header's example: a plan beats every set
C = "(a & b) | (~a & c)"
r = zplan.plan(C, blank(C), {"a": 1, "b": 1, "c": 1})
check(r["worst_case"]["cost"] == "2" and r["worst_case"]["plan"]["check"] == "a" and r["worst_case"]["checks_at_most"] == 2,
      "(a & b) | (~a & c): check a, then b or c - 2 in the worst case", r.get("worst_case"))
check(r["cheapest_set"] == {"cost": "3", "check_together": ["a", "b", "c"]}, "the cheapest SET there is all three: 3", r["cheapest_set"])
check(zplan.check(C, blank(C), {"a": 1, "b": 1, "c": 1}, r["worst_case"]["plan"]) == {"ok": True, "worst": "2", "why": None},
      "the plan is confirmed from scratch by the judge")
check(r["best_case"]["EARNED"]["cost"] == "2" and r["best_case"]["REFUTED"]["cost"] == "2", "best cases: 2 and 2", r["best_case"])

# 2. costs decide the order: a | b, a cheap and b dear - the worst case is both (6); the best case is a alone (1)
r = zplan.plan("a | b", blank("a | b"), {"a": 1, "b": 5})
check(r["worst_case"]["cost"] == "6" and r["worst_case"]["plan"]["check"] == "a" and r["best_case"]["EARNED"] == {"cost": "1", "if": [["a", T]]}
      and r["best_case"]["REFUTED"]["cost"] == "6" and r["cheapest_set"]["cost"] == "6",
      "a | b: worst 6 (the cheap one first), EARNED possible for 1, REFUTED only for 6", r)
# the dear ground first when it can end the matter alone: (a & b) | c with c dear - c must be checked anyway in the worst case
r = zplan.plan("(a & b) | c", blank("(a & b) | c"), {"a": 1, "b": 1, "c": 10})
check(r["worst_case"]["cost"] == "12", "(a & b) | c: 12 in the worst case", r["worst_case"]["cost"])
# fractions are costs too
r = zplan.plan("a & b", blank("a & b"), {"a": "1/2", "b": "1/3"})
check(r["worst_case"]["cost"] == "5/6" and r["best_case"]["REFUTED"]["cost"] == "1/3", "fractions: 1/2 + 1/3", r["worst_case"])

# 3. nothing to check; and a claim that is settled by what is already known
r = zplan.plan("a | b", {"a": T, "b": Z}, {"b": 1})
check(r["already"] and r["verdict"] == "EARNED" and "worst_case" not in r, "already EARNED: nothing to check", r)

# 4. refusals: a ground with no cost, too many grounds, a cost that is not one
check("refused" in zplan.plan("a | b", blank("a | b"), {"a": 1}), "a ground with no cost: refused")
big = " | ".join(f"g{i}" for i in range(zplan.PLAN_CAP + 1))
check("refused" in zplan.plan(big, blank(big), {f"g{i}": 1 for i in range(zplan.PLAN_CAP + 1)}), "more grounds than the cap: refused, not approximated")
for bad in ("-1", "much"):
    try:
        zplan.plan("a | b", blank("a | b"), {"a": bad, "b": 1}); check(False, f"the cost {bad!r} must be refused")
    except ValueError:
        check(True, "refused")

# 5. a ground no check can settle is never asked; when the claim rests on it, no plan settles the matter - said
r = zplan.plan("a | h", blank("a | h"), {"a": 1}, hold=("h",))
check("worst_case" not in r and "no plan" in r.get("no_plan", "") and r["held"] == ["h"] and r["best_case"]["EARNED"] == {"cost": "1", "if": [["a", T]]},
      "a | h, h held: no plan settles it, but EARNED is possible through a", r)
r = zplan.plan("a & (h | ~a)", blank("a & (h | ~a)"), {"a": 1}, hold=("h",))
check("no_plan" in r, "a & (h | ~a), h held: a = T leaves it on h", r)
r = zplan.plan("a | (h & ~a & a)", blank("a | (h & ~a & a)"), {"a": 1}, hold=("h",))
check(r.get("worst_case", {}).get("cost") == "1", "a held ground that does not matter does not block the plan", r)

# 6. EVERY PLAN LISTED, independently: for random small claims the least worst cost over all decision trees
OPS = ("&", "|", "->", "<->")
def rand_claim(rng, names, depth):
    if depth == 0 or rng.random() < 0.25:
        a = rng.choice(names); return a if rng.random() < 0.7 else "~" + a
    return f"({rand_claim(rng, names, depth - 1)} {rng.choice(OPS)} {rand_claim(rng, names, depth - 1)})"
def all_plans_least(text, m, costs, ask):
    """the least worst cost over every decision tree, by listing them (no memo, no pruning); None: none settles it"""
    if judge(text, m)["disposition"] in zplan.TERMINAL:
        return Fr(0)
    least = None
    for a in ask:
        if m[a] != Z:
            continue
        y = all_plans_least(text, dict(m, **{a: T}), costs, ask); n = all_plans_least(text, dict(m, **{a: F}), costs, ask)
        if y is None or n is None:
            continue
        w = costs[a] + max(y, n)
        least = w if least is None or w < least else least
    return least
rng = random.Random(20261127); same = total = with_plan = 0
for _ in range(120):
    names = ["a", "b", "c", "d"][:rng.randint(2, 4)]
    claim = rand_claim(rng, names, 3)
    at = sorted(_atoms(formalize(claim)))
    m = {a: (Z if rng.random() < 0.8 else rng.choice((T, F))) for a in at}
    costs = {a: Fr(rng.randint(1, 6)) for a in at}
    r = zplan.plan(claim, m, costs)
    if r.get("already"):
        continue
    total += 1
    want = all_plans_least(_show(formalize(claim)), dict(m), costs, at)
    got = Fr(r["worst_case"]["cost"]) if "worst_case" in r else None
    same += (want == got)
    if got is not None:
        with_plan += 1
        ck = zplan.check(claim, m, costs, r["worst_case"]["plan"])
        check(ck["ok"] and Fr(ck["worst"]) == got, f"the plan for {claim} is confirmed by the judge", ck)
        check(r["cheapest_set"] is not None and Fr(r["cheapest_set"]["cost"]) >= got, "a set is never cheaper than the plan", (claim, r["cheapest_set"], got))
check(same == total and total > 60 and with_plan > 60, f"the least over all plans, listed independently: {same} of {total}", (same, total, with_plan))

# 7. PLANTED: the better branch taken for the worse - the price claimed drops below the plan's own worst cost.
#    The example must be lopsided: on (a & b) | (~a & c) with equal costs both branches cost the same and the
#    sabotage changes nothing (seen 2026-11-27: the check stayed silent there).
S, SC = "a | b", {"a": 1, "b": 5}
zplan.MUTANT["best_branch"] = True
try:
    rm = zplan.plan(S, blank(S), SC)
finally:
    zplan.MUTANT.clear()
ckm = zplan.check(S, blank(S), SC, rm["worst_case"]["plan"])
check(rm["worst_case"]["cost"] == "1" and ckm["ok"] and ckm["worst"] == "6",
      "the sabotage is seen: 1 claimed, the judge's re-walk of that same plan gives 6", (rm["worst_case"], ckm))
check(zplan.plan(S, blank(S), SC)["worst_case"]["cost"] == "6", "with the switch off the price is 6 again")
# and a forged plan is refused by the checker
forged = {"check": "a", "cost": "1", "if_true": {"verdict": "EARNED"}, "if_false": {"verdict": "REFUTED"}}
check(not zplan.check(C, blank(C), {"a": 1, "b": 1, "c": 1}, forged)["ok"], "a plan whose leaves are not the judge's dispositions is refused")

print(f"{CHECKS} checks, {len(FAILS)} failed; plans compared with the independent listing: {same} of {total}")
print("ZPLAN GREEN" if not FAILS else "ZPLAN RED")
sys.exit(1 if FAILS else 0)
