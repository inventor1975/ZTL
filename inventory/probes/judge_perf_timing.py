# -*- coding: utf-8 -*-
"""
judge_perf_timing — the judge's running time as a function of PYTHONHASHSEED.

For each SHAPE and each hash seed, a fresh interpreter (the seed is fixed at
interpreter start, so it must be a subprocess) runs the claim once through the
judge of the given tree and reports the CPU seconds of that call alone, with the
verdict/grade/disposition it produced. The summary per shape is min / median /
max over the seeds, and whether every seed gave the same answer.

Run:
  python3 inventory/probes/judge_perf_timing.py --tree OLD_TREE --seeds 1-50
  python3 inventory/probes/judge_perf_timing.py --tree . --seeds 1-50 --shape S1
"""
import argparse
import json
import os
import statistics
import subprocess
import sys

# name -> (kind, payload, what)
SHAPES = {
    "S1": ("doc12", None, "studio doc, x in [0,50], (x<=1) ^ ... ^ (x<=12) — above the cap, "
                          "run with zfl.validate stubbed"),
    "S2": ("doc", {"claim": " ^ ".join(f"(x <= {j})" for j in range(1, 10)),
                   "rows": [{"name": "x", "means": "x", "status": "unverified",
                             "value": "[0,50]"}]},
           "studio doc, (x<=1) ^ ... ^ (x<=9) — the largest the cap admits"),
    "S3": ("prop", " ^ ".join(f"a{i}" for i in range(10)),
           "a0 ^ a1 ^ ... ^ a9, all unverified"),
    "S4": ("prop", " & ".join(f"a{i}" for i in range(10)),
           "a0 & ... & a9, all unverified"),
    "S5": ("prop", "(" + " ^ ".join(f"a{i}" for i in range(10)) + ") & ("
           + " | ".join(f"~a{i}" for i in range(10)) + ")",
           "every atom twice: (a0 ^ .. ^ a9) & (~a0 | .. | ~a9)"),
    "S6": ("prop", " & ".join(f"(a{i} & ~a{i})" for i in range(10)),
           "(a0 & ~a0) & ... : F, hereditary — no witness exists, the full walk"),
    "S7": ("prop", " -> ".join(f"(a{i} = a{(i + 1) % 10})" for i in range(10)),
           "a ring of equivalences under implication, every atom twice"),
}

CHILD = r'''
import sys, time, json
sys.path.insert(0, sys.argv[1])
kind, payload = sys.argv[2], json.loads(sys.argv[3])
if kind == "prop":
    import ztljudge
    t = time.process_time(); r = ztljudge.judge(payload, {}); dt = time.process_time() - t
    out = [r["verdict"], r["grade"], r["disposition"], r["joint"]]
else:
    import zfl
    if kind == "doc12":
        zfl.validate = lambda doc: []
        payload = {"claim": " ^ ".join(f"(x <= {j})" for j in range(1, 13)),
                   "rows": [{"name": "x", "means": "x", "status": "unverified",
                             "value": "[0,50]"}]}
    t = time.process_time(); r = zfl.run(payload); dt = time.process_time() - t
    n = r["report"]["numeric"]
    out = [n.get("verdict"), n.get("grade"), n["disposition"]]
print(json.dumps({"s": dt, "out": out}))
'''


def one(tree, shape, seed, timeout):
    kind, payload, _ = SHAPES[shape]
    env = dict(os.environ, PYTHONHASHSEED=str(seed))
    try:
        p = subprocess.run([sys.executable, "-c", CHILD, os.path.abspath(tree), kind,
                            json.dumps(payload)], env=env, capture_output=True,
                           text=True, timeout=timeout)
        return json.loads(p.stdout.strip().splitlines()[-1])
    except subprocess.TimeoutExpired:
        return {"s": float("inf"), "out": ["TIMEOUT"]}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tree", default=".")
    ap.add_argument("--seeds", default="1-50")
    ap.add_argument("--shape", default=None)
    ap.add_argument("--timeout", type=float, default=300)
    ap.add_argument("--json", default=None)
    a = ap.parse_args()
    lo, hi = map(int, a.seeds.split("-"))
    shapes = [a.shape] if a.shape else list(SHAPES)
    res = {}
    print(f"tree {a.tree}, PYTHONHASHSEED {lo}..{hi}")
    print("| shape | min s | median s | max s | same answer on every seed |")
    print("|---|---|---|---|---|")
    for sh in shapes:
        runs = [one(a.tree, sh, s, a.timeout) for s in range(lo, hi + 1)]
        ts = [r["s"] for r in runs]
        same = len({json.dumps(r["out"]) for r in runs}) == 1
        res[sh] = {"times": ts, "outs": [r["out"] for r in runs]}
        print(f"| {sh} | {min(ts):.3f} | {statistics.median(ts):.3f} | {max(ts):.3f} | "
              f"{'yes' if same else 'NO'} {runs[0]['out']} |", flush=True)
    if a.json:
        json.dump(res, open(a.json, "w"))


if __name__ == "__main__":
    main()
