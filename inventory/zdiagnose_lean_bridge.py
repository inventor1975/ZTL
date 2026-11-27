# -*- coding: utf-8 -*-
"""
zdiagnose ↔ lean/ZDiagnose.lean — conflicts and diagnoses against their definitions, computed by the kernel (2026-11-27).

`lean/ZDiagnose.lean` proves (no axioms) that on the claim ⋀_c ⋁_{p∈c} ¬p the sets that can EARN it are exactly the
sets that meet every conflict, so the diagnoses are the minimal hitting sets (`diagnoses_are_hitting_sets`); the
conflicts are `ZBackward.fam` of the "refuted" oracle. Three checks tie the Python to it:

  A. THE JUDGE IS THE MODEL: for random conflict families over n ≤ 5 premises, the worlds in which the Python judge
     EARNS `zdiagnose._formula(conflicts)` are exactly the worlds the kernel's `earnedW` accepts (all 3^n worlds);
  B. DIAGNOSES: `zbackward.backward(formula, all dirty, "EARNED")["possible"]` equals the kernel's `fam (hitsAll cs)`;
  C. CONFLICTS: on the cases of test_zdiagnose.py, `zdiagnose.diagnose(...)["conflicts"]` equals the kernel's `fam` of
     the numeric judge's "refuted" oracle, asked for every one of the 2^n kept sets.
MUTATION: one conflict dropped from a family -> check B differs.

Run:  python3 inventory/zdiagnose_lean_bridge.py   -> ZDIAGNOSE LEAN BRIDGE GREEN
"""
import itertools
import os
import random
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
import zbackward as ZB                 # noqa: E402
import zdiagnose as D                  # noqa: E402
from ztl import T, F, Z                # noqa: E402

LEAN = os.path.join(ROOT, "lean")


def mask(S, names):
    return "[" + ", ".join("true" if n in S else "false" for n in names) + "]"


def lw(w):
    return "[" + ", ".join("none" if x is None else f"some {'true' if x else 'false'}" for x in w) + "]"


def antichain(rnd, names):
    out = []
    for _ in range(rnd.randint(1, 4)):
        S = frozenset(rnd.sample(names, rnd.randint(1, len(names))))
        if not any(S <= c or c <= S for c in out):
            out.append(S)
    return out


def run_lean(lines):
    fd, path = tempfile.mkstemp(prefix="zdiagnose_bridge_", suffix=".lean", dir=LEAN)
    with os.fdopen(fd, "w", encoding="utf-8") as fh:
        fh.write("\n".join(["import ZDiagnose", "open ZBackward ZDiagnose", ""] + lines) + "\n")
    try:
        r = subprocess.run(["lake", "env", "lean", path], cwd=LEAN, capture_output=True, text=True, timeout=1800)
    finally:
        os.unlink(path)
    if r.returncode != 0:
        raise SystemExit("LEAN FAILED:\n" + (r.stdout + r.stderr)[-3000:])
    out = {}
    for l in r.stdout.splitlines():
        if l.startswith("K"):
            head, rest = l.split(" ", 1)
            out[head] = rest
    return out


def idx(fam):
    return sorted(sorted(x) for x in fam)


def main():
    ok = fail = 0
    rnd = random.Random(20261127)
    jobs = []
    for i in range(150):
        n = rnd.randint(1, 5)
        names = [f"p{j}" for j in range(n)]
        cs = antichain(rnd, names)
        phi = D._formula([tuple(sorted(c)) for c in cs])
        earned = []
        for w in itertools.product((None, False, True), repeat=n):
            m = {p: (Z if x is None else (T if x else F)) for p, x in zip(names, w)}
            if ZB._disposition(phi, m) == "EARNED":
                earned.append(w)
        r = ZB.backward(phi, {p: Z for p in names}, "EARNED")
        jobs.append((names, cs, earned, r))
    lines = []
    for k, (names, cs, earned, r) in enumerate(jobs):
        csl = "[" + ", ".join(mask(c, names) for c in cs) + "]"
        n = len(names)
        lines.append(f"def c{k} : List (List Bool) := {csl}")
        lines.append(f'#eval IO.println s!"KA{k} {{((worlds {n}).filter (earnedW c{k})).length}} '
                     f'{{(worlds {n}).filter (earnedW c{k}) == {"[" + ", ".join(lw(w) for w in earned) + "]"}}}"')
        lines.append(f'#eval IO.println s!"KB{k} {{famIdx (hitsAll c{k}) {n}}}"')
    # C: conflicts of the zdiagnose stand's cases
    import importlib.util
    cases_c = [("a*b", {"a": ((1, 1.1), (0.5, 2)), "b": ((2, 2.2), (1, 4))}, (3.0, 3.1), (0.5, 2)),
               ("a*b", {"a": ((1, 1.1), (1, 1.2)), "b": ((2, 2.2), (2, 2.3))}, (3.0, 3.1), (0.5, 2)),
               ("a*b", {"a": ((1, 1.1), (0.5, 2)), "b": ((2, 2.2), (1, 4))}, (2.1, 2.2), (0.5, 2)),
               ("a+b*c", {"a": ((1, 2), (0, 3)), "b": ((1, 1.5), (0.5, 3)), "c": ((2, 3), (1, 4))}, (12, 13), (0.8, 1.25)),
               ("a+b*c", {"a": ((1, 2), (0, 3)), "b": ((1, 1.5), (0.5, 3)), "c": ((2, 3), (1, 4))}, (9, 9.5), (0.5, 2))]
    cres = []
    for k, (expr, P, meas, lr) in enumerate(cases_c):
        names = list(P) + [D.LAW]
        table = [S for kk in range(len(names) + 1) for S in itertools.combinations(names, kk)
                 if D._conflict(expr, P, set(S), meas, lr)]
        r = D.diagnose(expr, P, meas, law_relaxed=lr)
        cres.append((names, r))
        tl = "[" + ", ".join(mask(set(S), names) for S in table) + "]"
        lines.append(f"def t{k} : List (List Bool) := {tl}")
        lines.append(f'#eval IO.println s!"KC{k} {{famIdx (fun s => t{k}.contains s) {len(names)}}}"')
    got = run_lean(lines)
    a_ok = b_ok = 0
    for k, (names, cs, earned, r) in enumerate(jobs):
        a_good = got[f"KA{k}"].split()[1] == "true"
        kb = idx(eval(got[f"KB{k}"]))
        pb = idx([[names.index(p) for p in S] for S in r["possible"]])
        b_good = kb == pb
        a_ok += a_good; b_ok += b_good
        if not (a_good and b_good):
            fail += 1; print("  DIFF", k, names, [sorted(c) for c in cs], got[f"KA{k}"], kb, pb)
        else:
            ok += 1
    print(f"A judge EARNED == earnedW on all 3^n worlds: {a_ok}/{len(jobs)};  B diagnoses == fam(hitsAll): {b_ok}/{len(jobs)}")
    c_ok = 0
    for k, (names, r) in enumerate(cres):
        kc = idx(eval(got[f"KC{k}"]))
        pc = idx([[names.index(p) for p in S] for S in r["conflicts"]]) if r["conflicts"] != [()] else [[]]
        if kc == pc:
            c_ok += 1; ok += 1
        else:
            fail += 1; print("  DIFF C", k, kc, pc)
    print(f"C conflicts == fam(refuted oracle): {c_ok}/{len(cres)}  (families: "
          f"{[len(r['conflicts']) for _, r in cres]})")
    # MUTATION
    names, cs, earned, r = next(j for j in jobs if len(j[1]) >= 2)
    kk = jobs.index((names, cs, earned, r))
    dropped = idx(eval(got[f"KB{kk}"]))
    mut_lines = [f"def m : List (List Bool) := [{', '.join(mask(c, names) for c in cs[1:])}]",
                 f'#eval IO.println s!"KM {{famIdx (hitsAll m) {len(names)}}}"']
    caught = idx(eval(run_lean(mut_lines)["KM"])) != dropped
    print(f"mutation (one conflict dropped): {'caught' if caught else 'NOT CAUGHT'}")
    if fail == 0 and caught:
        print("ZDIAGNOSE LEAN BRIDGE GREEN")
    else:
        print("ZDIAGNOSE LEAN BRIDGE RED"); sys.exit(1)


if __name__ == "__main__":
    main()
