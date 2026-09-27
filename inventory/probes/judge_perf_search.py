# -*- coding: utf-8 -*-
"""
judge_perf_search — the new warranty check's worst case, hunted (2026-09-27).

`search`: 400 seeded random formulas over 10 atoms with 15-40 leaves (so atoms
repeat, which is where `zverify._only` must split), judged with an empty
marking (every atom unverified); prints the 8 slowest and the median, and saves
them. `replay`: judges the saved 8 on another tree, to set old beside new.

Run:
  PYTHONHASHSEED=1 python3 inventory/probes/judge_perf_search.py NEW_TREE search 400 top.json
  PYTHONHASHSEED=1 python3 inventory/probes/judge_perf_search.py OLD_TREE replay top.json
"""
import sys, time, random, json
sys.path.insert(0, sys.argv[1])
import ztljudge
mode = sys.argv[2]
rnd = random.Random(7)
OPS = ["&", "|", "^", "->", "="]
def gen(n_leaves, atoms):
    if n_leaves == 1:
        return rnd.choice(atoms) if rnd.random() > 0.1 else "~" + rnd.choice(atoms)
    k = rnd.randint(1, n_leaves - 1)
    s = f"({gen(k, atoms)} {rnd.choice(OPS)} {gen(n_leaves - k, atoms)})"
    return "~" + s if rnd.random() < 0.1 else s
if mode == "search":
    out = []
    for i in range(int(sys.argv[3])):
        atoms = [f"a{j}" for j in range(10)]
        text = gen(rnd.choice([15, 20, 30, 40]), atoms)
        t = time.process_time(); r = ztljudge.judge(text, {}); dt = time.process_time() - t
        out.append((dt, text, r["grade"]))
    out.sort(reverse=True)
    json.dump(out[:8], open(sys.argv[4], "w"))
    for dt, text, g in out[:8]: print(f"{dt:7.3f} s {g:20s} {text[:90]}")
    print("median", sorted(x[0] for x in out)[len(out)//2])
else:
    for dt, text, g in json.load(open(sys.argv[3])):
        t = time.process_time(); r = ztljudge.judge(text, {}); d2 = time.process_time() - t
        print(f"old {d2:7.3f} s (new {dt:.3f} s) {r['grade']}")
