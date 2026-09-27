# -*- coding: utf-8 -*-
"""
test_judge_perf — the judge's warranty is computed without a walk, and answers
exactly as the walk did, in time that does not depend on the hash seed.

Until 2026-09-27 `zverify.hereditary_bit` and `stable_bit` ended in a walk over
all 3^n refinements / 2^n completions that stopped at the first disagreeing
reading — and where that reading sat depended on the order of the marks, i.e.
on PYTHONHASHSEED. `(x<=1) ^ ... ^ (x<=12)` in a studio table took 0.2 s on one
seed and 16 s on another. Now `zverify._only` decides the same question exactly
(reachable value sets over independent subtrees, Shannon splits only on atoms
that occur twice). The walk stays as the definition and the fallback.

Pinned here:
  1. equivalence with the walk: forcing the old path (`_only` -> None) must give
     the SAME `grade` on seeded (formula, marking) pairs, and the SAME `judge`
     output (verdict, grade, disposition, why, joint, pending, ...) on seeded
     claims — including budgets, constants T/F/Z and absent (E) atoms;
  2. a time bound on the worst known shape, on three hash seeds, each in a
     fresh interpreter: the 12-comparison claim must judge in < 1 s CPU (it took
     up to 16 s before on this machine; 0.03 s after).
Run: python3 test_judge_perf.py  ->  JUDGE PERF GREEN
"""
import json
import os
import random
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "inventory", "probes"))

import zverify                                          # noqa: E402
import ztljudge                                         # noqa: E402
from ztl import T, F                                    # noqa: E402
import judge_equiv                                      # noqa: E402

CHECKS = 0


def check(cond, what):
    global CHECKS
    CHECKS += 1
    if not cond:
        raise SystemExit(f"FAIL: {what}")


NEW = zverify._only


def old_path(fn, *args):
    """Run `fn` with the new exact check switched off: the walk answers."""
    zverify._only = lambda *a: None
    try:
        return fn(*args)
    finally:
        zverify._only = NEW


# ---- 1a. grade on (formula, marking) pairs, budgets included
rnd = random.Random(20260927)
OPS = ["and", "or", "imp", "xor", "xnor"]


def gen(d, ats):
    if d == 0 or rnd.random() < 0.2:
        return rnd.choice(("T", "F", "Z")) if rnd.random() < 0.07 else rnd.choice(ats)
    if rnd.random() < 0.25:
        return ("not", gen(d - 1, ats))
    return (rnd.choice(OPS), gen(d - 1, ats), gen(d - 1, ats))


t0 = time.time()
n_grade = 0
for _ in range(6000):
    ats = [f"p{i}" for i in range(rnd.randint(1, 7))]
    phi = gen(rnd.randint(1, 6), ats)
    mk = {a: rnd.choice(("M", "M", T, F)) for a in ats}
    budget = rnd.choice([None, None, None, 9, 81, 729])
    new = zverify.grade(phi, mk, budget)
    old = old_path(zverify.grade, phi, mk, budget)
    check(new == old, f"grade differs: {phi} {mk} budget={budget}: new {new} old {old}")
    n_grade += 1

# ---- 1b. the whole judge output on seeded claims (the equivalence stream)
n_judge = 0
for i in range(1500):
    text, marks = judge_equiv.prop_claim(i)
    new = ztljudge.judge(text, marks)
    old = old_path(ztljudge.judge, text, marks)
    check(new == old, f"judge differs on claim {i}: {text} {marks}")
    n_judge += 1
t_eq = time.time() - t0

# ---- 2. the worst known shape, three hash seeds, fresh interpreters
CHILD = r'''
import sys, time, json
sys.path.insert(0, sys.argv[1])
import zfl
zfl.validate = lambda doc: []      # above the cap on purpose: the cause, not the guard
doc = {"claim": " ^ ".join(f"(x <= {j})" for j in range(1, 13)),
       "rows": [{"name": "x", "means": "x", "status": "unverified", "value": "[0,50]"}]}
t = time.process_time(); r = zfl.run(doc); dt = time.process_time() - t
n = r["report"]["numeric"]
print(json.dumps([dt, n["disposition"], n["grade"], n["verdict"]]))
'''
outs = set()
for seed in (2, 3, 4):
    p = subprocess.run([sys.executable, "-c", CHILD, HERE],
                       env=dict(os.environ, PYTHONHASHSEED=str(seed)),
                       capture_output=True, text=True, timeout=120)
    dt, *ans = json.loads(p.stdout.strip().splitlines()[-1])
    check(dt < 1.0, f"12-comparison claim took {dt:.2f} s CPU on PYTHONHASHSEED={seed}")
    outs.add(tuple(ans))
check(outs == {("OPEN", "until-verification", "F")},
      f"12-comparison claim answered {outs}, expected OPEN / until-verification / F")

print(f"JUDGE PERF GREEN ({CHECKS} checks: {n_grade} grades and {n_judge} judge "
      f"outputs equal to the walk in {t_eq:.0f} s; worst shape < 1 s on 3 seeds)")
