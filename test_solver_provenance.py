# -*- coding: utf-8 -*-
"""
test_solver_provenance — an unknown is the question, not a source.

The curator's word, 2026-09-24, on two findings put to him:
  (1) "no solution" resting on a ground still on credit is not a refutation
      yet: `x == k & x == j` with k on credit came back REFUTED; now it is
      ON CREDIT, toward F, with "document k";
  (2) a value derived from equations over constants and earned rows is
      earned: x + y = 10, x - y = 2 came back 6 and 4 ON CREDIT, the other
      unknown counted as a credit source.
Every derived quantity now records its GROUNDS: the rows with a bound it
rests on, transitively; `?` spans the line and grounds nothing.

While building it, MEASURED: a pinned row read as a constant dropped out of
the provenance of the bound it produced, so `x <= t` with t on credit gave
x an EARNED bound from nothing, and 28 cases of the solver sweep carried an
earned bound derived from a credit total, invisible to that sweep's own
invariant (whose sources were empty). The independent check here does not
trust the solver's record: an EARNED solved value may not coexist with a
credit row the claim reads.
Run: python3 test_solver_provenance.py  ->  SOLVER PROVENANCE GREEN
"""
import os
import sys
from itertools import product

import zfl
from znumjudge import parse_quantities
from znumsolve import solve_claim

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "conformance"))
import solver_table                                               # noqa: E402

CHECKS = 0


def check(cond, what):
    global CHECKS
    CHECKS += 1
    if not cond:
        print("FAIL:", what)
        sys.exit(1)


def row(name, value, earned):
    r = {"name": name, "means": "a quantity", "value": value,
         "status": "verified" if earned else "unverified"}
    if earned:
        r["ground"] = "doc-1"
    return r


def numeric(rows, claim):
    r = zfl.run({"rows": rows, "claim": claim})
    check(r["ok"], f"{claim}: {r.get('issues')}")
    return r["report"]["numeric"]


# (2) the other unknown is not a source
n = numeric([row("x", "?", False), row("y", "?", False)], "x + y == 10 & x - y == 2")
check(n["disposition"] == "EARNED" and all(v["prov"] == "earned" for v in n["solved"].values()),
      f"x + y = 10, x - y = 2 from constants is earned: {n['disposition']} {n['solved']}")
n = numeric([row("x", "?", False), row("y", "?", False), row("t", "10", False)], "x + y == t & x - y == 2")
check(n["disposition"] == "ON CREDIT" and all(v["prov"] == "credit" for v in n["solved"].values()),
      f"... and from a credit t it is credit: {n['solved']}")
# (1) no solution on credit is ON CREDIT toward F; on earned grounds REFUTED
for earned_k, want in ((False, "ON CREDIT"), (True, "REFUTED")):
    for claim in ("x == k & x == j", "x*x + k == 0"):
        n = numeric([row("x", "?", False), row("k", "5", earned_k), row("j", "6", True)], claim)
        check(n["disposition"] == want, f"{claim}, k earned={earned_k}: {n['disposition']}, want {want}")
        if want == "ON CREDIT":
            check(n.get("polarity") == "toward F" and "document k" in n["next_check"],
                  f"{claim}: leans to F and names the cure: {n.get('polarity')} {n['next_check']}")
# the leak found while building it
n = numeric([row("x", "?", False), row("t", "10", False)], "x <= t")
check(n["solved"]["x"]["prov"] == "credit" and n["solved"]["x"]["from"] == ["t"],
      f"x <= t with t on credit: x is credit, from t: {n['solved']['x']}")
# a literal interval in the claim no longer crashes the solver
r = zfl.run({"rows": [row("x", "?", False)], "claim": "x == [3,4]"})
check(r["ok"] and r["report"]["numeric"]["disposition"] == "OPEN"
      and not any("_lit" in c for c in r["report"]["numeric"]["next_check"]),
      f"x == [3,4]: {r.get('issues') or r['report']['numeric']}")

# the independent check over the solver sweep: an EARNED solved value may not
# coexist with a credit row, other than itself, that the claim reads and that
# carries a bound
pool = earned = 0
for formula, data in solver_table.cases():
    q, m = parse_quantities(data)
    r = solve_claim(formula, q, m)
    read = {nm for nm in q if nm in formula.replace("sum(", " ").replace(",", " ").replace(")", " ").split()}
    for nm, v in (r.get("solved") or {}).items():
        pool += 1
        if v["prov"] != "earned":
            continue
        earned += 1
        credit_rows = sorted(o for o in read - {nm}
                             if q[o]["prov"] == "credit" and not (q[o]["lo"] == -float("inf") and q[o]["hi"] == float("inf")))
        check(not credit_rows, f"EARNED {nm} beside credit rows {credit_rows}: {formula} | {data}")
check(earned > 0, f"the sweep produced earned values to check ({earned})")
print(f"SOLVER PROVENANCE GREEN — {CHECKS} checks; {pool} solved values in the sweep, "
      f"{earned} earned, none beside a credit row the claim reads")
