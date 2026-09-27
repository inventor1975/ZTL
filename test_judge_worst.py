# -*- coding: utf-8 -*-
"""
test_judge_worst — the judge's worst cases after the 2026-09-27 speed-up,
pinned with a time bound (2026-09-27, the worst-case search).

The public studio should answer one request in < 0.5 s of one core. Each check
below runs a pinned case through the REAL path (zfl.run with its validator and
cap in force, unless it says otherwise) under a CPU budget, so the stand stays
fast however slow the case is: a case over budget is cut, not waited for.

RED on master @ 7a432ce — three components the atom cap does not bound, and
one (W4) that bounds how far the cap may be raised:

  W1  `ztljudge._lazy` evaluates both children of every binary node (line 292)
      and then, for `->`, re-reads the node as `~a | b` and evaluates both
      children AGAIN: each nested implication doubles the work. 20 nested `->`
      over ONE atom — 141 characters, atom count 1 — pass the validator and
      cost ~15 s in zfl.run. Not a wrong verdict; a cost.
  W2  `zfl.what_to_check` (the reverse pass, `zbackward.backward` x 3 targets)
      calls the whole judge 3 * sum_{k<=4} C(u,k) 2^k times — 1,419 at u = 6
      unverified inputs — and each call grows with the claim's length. The
      grid claim below (10 atoms, 6 unverified, 308 characters): ~8 s; ~2.8 s
      even with W1 fixed. This is the "~1 s at 10 atoms" on old and new code.
  W3  the epoch floor judges the claim twice per declared `expires_on` event,
      and events are not capped (rows are not): 200 events on rows the claim
      never reads (32 KB) cost ~15 s.
  W4  `zverify._only` is exponential in the marked atoms that occur more than
      once: 16 unverified atoms, each 13-14 times, a 1753-character balanced
      claim — judge ~64 s even with W1 fixed. Above today's cap (10), so not
      reachable publicly; it is what a raised cap would expose.

GREEN controls (what the cap already bounds): the shapes built to defeat
`zverify._only` — xor/biconditional cycles, grids, atoms 2-4 times — judge in
well under 0.5 s at 10 atoms, all unverified. And the proposed W1 fix (the
`imp` branch computed from the children already in hand) is checked to be the
same function as `_lazy`, so adopting it cannot move a lazy value or a label.

Run: python3 test_judge_worst.py   ->  JUDGE WORST GREEN, or RED naming each.
Not registered in run_all.py (registration changes the counted stands).
"""
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "inventory", "probes"))

import zfl                                             # noqa: E402
import ztljudge                                        # noqa: E402
import judge_worst as W                                # noqa: E402

BOUND = 0.5          # seconds of one core per request (the proposal's target)
BUDGET = 1.5         # a case is cut here: over the bound either way
CHECKS, FAILS = 0, []


def check(cond, what):
    global CHECKS
    CHECKS += 1
    if not cond:
        FAILS.append(what)
        print(f"FAIL: {what}")


def run_real(doc):
    """zfl.run exactly as the studio calls it (validator and cap in force)."""
    issues = [i["code"] for i in zfl.validate(doc) if i["level"] == "error"]
    t, r = W.timed(lambda: zfl.run(doc), BUDGET)
    return issues, t


def fmt(t):
    return f"> {BUDGET} s (cut)" if t is None else f"{t:.2f} s"


# ---- W1: nested implications over one atom
chain = "a"
for _ in range(20):
    chain = f"({chain} -> a)"
doc_w1 = {"claim": chain, "rows": [{"name": "a", "means": "a", "status": "unverified"}]}
issues, t = run_real(doc_w1)
check(not issues, f"W1 the 20-deep implication chain passes the validator ({issues})")
check(t is not None and t < BOUND,
      f"W1 20 nested '->' over one atom ({len(chain)} chars, atom count 1): zfl.run "
      f"{fmt(t)} — _lazy re-evaluates both children of every implication")

# ---- W2: the reverse pass on the worst grid found (verbatim)
GRID = ("((((((((((((((((((((a6 <-> a7) | (a0 <-> a3)) & (a1 <-> a2)) & (a5 <-> a6)) | "
        "(a4 ^ a7)) -> (a7 <-> a0)) | (a7 <-> a8)) | (a8 ^ a9)) -> (a2 <-> a5)) -> "
        "(a5 <-> a8)) -> (a1 <-> a4)) -> (a8 ^ a1)) & (a9 ^ a2)) -> (a2 <-> a3)) -> "
        "(a0 <-> a1)) -> (a9 ^ a0)) | (a4 ^ a5)) -> (a3 ^ a6)) & (a6 ^ a9)) | (a3 <-> a4))")
STAT = {"a0": "unverified", "a1": "unverified", "a2": "verified", "a3": "refuted",
        "a4": "unverified", "a5": "refuted", "a6": "unverified", "a7": "verified",
        "a8": "unverified", "a9": "unverified"}
rows = []
for a, st in STAT.items():
    row = {"name": a, "means": a, "status": st}
    if st != "unverified":
        row["ground"] = f"doc-{a}"
    rows.append(row)
doc_w2 = {"claim": GRID, "rows": rows}
issues, t = run_real(doc_w2)
check(not issues, f"W2 the grid document passes the validator ({issues})")
check(t is not None and t < BOUND,
      f"W2 grid claim, 10 atoms, 6 unverified, {len(GRID)} chars: zfl.run {fmt(t)} — "
      f"what_to_check calls judge ~1,419 times")
W.use_fixed_lazy(True)
_, t_fix = run_real(doc_w2)
W.use_fixed_lazy(False)
check(t_fix is not None and t_fix < BOUND,
      f"W2 the same with W1's fix in place: {fmt(t_fix)} — the reverse pass alone")

# ---- W3: the epoch floor, 200 events on rows the claim never reads
claim3, names3 = W.fam_grid(10, random.Random("epoch"))
rows3 = [{"name": a, "means": a, "status": "unverified"} for a in names3]
for i in range(200):
    rows3.append({"name": f"g{i}", "means": "g", "status": "verified",
                  "ground": f"doc-{i}", "expires_on": f"ev{i}"})
    rows3.append({"name": f"ev{i}", "means": "an event", "status": "unverified"})
doc_w3 = {"claim": claim3, "rows": rows3}
issues, t = run_real(doc_w3)
check(not issues, f"W3 the 200-event document passes the validator ({issues})")
check(t is not None and t < BOUND,
      f"W3 200 expiry events on rows the claim never reads: zfl.run {fmt(t)} — "
      f"two judges per event, events uncapped")

# ---- W4: zverify._only's own tail — found by search at 16 atoms (above today's
# cap of 10; it bounds how far the cap may rise). Every atom 13-14 times in a
# 1753-character balanced claim; one grade builds 57,838 Shannon residues.
# Measured with the W1 fix in place: judge ~64 s. Five sibling seeds: <= 0.36 s.
claim4, names4 = W.fam_longbal(16, random.Random("judgescan:longbal:16:2000:2"), 2000)
W.use_fixed_lazy(True)
t4, _ = W.timed(lambda: ztljudge.judge(claim4, {a: "Z" for a in names4}), BUDGET)
W.use_fixed_lazy(False)
check(t4 is not None and t4 < BOUND,
      f"W4 16 unverified atoms, each 13-14 times, {len(claim4)} chars: judge {fmt(t4)} "
      f"(with W1 fixed) — zverify._only splits on every repeated mark")

# ---- controls: what the atom cap bounds today
for fam in ("xorcycle", "grid", "repeat", "random"):
    worst = 0.0
    for k in range(3):
        rnd = random.Random(f"{fam}:unverified:10:{k}")
        claim, names = W.FAMILIES[fam](10, rnd)
        m = {a: "Z" for a in names}
        t, _ = W.timed(lambda: ztljudge.judge(claim, m), BUDGET)
        worst = max(worst, BUDGET if t is None else t)
    check(worst < BOUND, f"control {fam}: 10 unverified atoms, judge worst {worst:.3f} s")

# ---- the proposed W1 fix is the same function as _lazy
import redteam_logic_oracle as O                       # noqa: E402
rnd = random.Random("lazy-fix:20260927")
diff = 0
for _ in range(20000):
    ats = [f"p{j}" for j in range(rnd.randint(1, 6))]
    phi = O.random_formula(rnd, rnd.randint(0, 7), ats)
    m = {a: rnd.choice("TFZ") for a in ats if rnd.random() < 0.7}
    diff += W._LAZY_ORIG(phi, m) != W.lazy_fixed(phi, m)
check(diff == 0, f"the proposed _lazy fix differs from _lazy on {diff} of 20000 formulas")

if FAILS:
    print(f"JUDGE WORST RED: {len(FAILS)} of {CHECKS} checks fail — see above")
    sys.exit(1)
print(f"JUDGE WORST GREEN ({CHECKS} checks)")
