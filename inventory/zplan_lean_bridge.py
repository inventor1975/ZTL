# -*- coding: utf-8 -*-
"""
zplan ↔ lean/ZPlan.lean — the cheapest plan of checks against its definition, computed by the kernel (2026-11-27).

`lean/ZPlan.lean` proves, with no axioms, that the recursion `opt` is the least worst cost over ALL plans of checks
that settle a claim (`opt_le`: no valid plan is cheaper; `opt_attained`: a valid plan costs exactly that; `optimal`).
"Settled" there is the kernel's own reading: `earnedR` or `refutedR` (lean/ZRead.lean). This stand ties the Python
answer to that definition:

  for seeded random claims, markings and whole-number costs, the claim itself is written into a Lean file as a
  formula, and Lean evaluates `opt cost φ k dirty marking`. The number must equal `zplan.plan(...)`'s worst-case
  cost (0 when the claim is already settled). So here the oracle on the Lean side is NOT the Python judge: both the
  judging and the search are redone by Lean from the formula.

  a part of the cases (few dirty grounds) is also stated as `example : opt … = n := by decide` — checked by the
  kernel, not by the evaluator.

MUTATION, two of them: (1) the Python module with the better branch taken for the worse must differ from Lean on
some case - "caught"; (2) a wrong number stated as a theorem must be refused by the kernel.

Costs are whole numbers here (the theorem is over Nat; zplan takes fractions - a common denominator turns them into
whole numbers, and the order of sums and maxima is the same).

Run:  python3 inventory/zplan_lean_bridge.py   -> ZPLAN LEAN BRIDGE GREEN
"""
import os
import random
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
import zplan                            # noqa: E402
from ztl import T, F, Z                 # noqa: E402

LEAN = os.path.join(ROOT, "lean")
OPS = ["and", "or", "imp", "xor", "xnor"]
CON = {"and": "conj", "or": "disj", "imp": "imp", "xor": "xor", "xnor": "xnor"}
DECIDE_UP_TO = 3            # dirty grounds: cases this small are ALSO stated as theorems (`by decide`)
DECIDE_AT_MOST = 40         # ... the first so many of them (the kernel is slower than the evaluator)


def gen(rnd, leaves):
    if len(leaves) == 1:
        return ("not", leaves[0]) if rnd.random() < 0.2 else leaves[0]
    k = rnd.randint(1, len(leaves) - 1)
    node = (rnd.choice(OPS), gen(rnd, leaves[:k]), gen(rnd, leaves[k:]))
    return ("not", node) if rnd.random() < 0.15 else node


def cases(seed=20261127, n_cases=400):
    rnd = random.Random(seed)
    out = []
    for _ in range(n_cases):
        n_atoms = rnd.randint(2, 5)
        atoms = [f"a{j}" for j in range(n_atoms)]
        leaves = atoms + ([rnd.choice(atoms)] if rnd.random() < 0.4 else [])      # some grounds repeated
        rnd.shuffle(leaves)
        phi = gen(rnd, leaves)
        marking = {a: rnd.choice([Z, Z, Z, Z, T, F]) for a in atoms}
        costs = {a: rnd.randint(1, 7) for a in atoms}
        out.append((phi, atoms, marking, costs))
    return out


def lean_fm(phi, idx):
    if isinstance(phi, str):
        return f"(.atom {idx[phi]})"
    if phi[0] == "not":
        return f"(.neg {lean_fm(phi[1], idx)})"
    return f"(.{CON[phi[0]]} {lean_fm(phi[1], idx)} {lean_fm(phi[2], idx)})"


def lean_fun(pairs, default):
    """a function Nat → α by cases on the ground's number"""
    return "fun n => " + "".join(f"if n = {i} then {x} else " for i, x in pairs) + default


def lean_terms(phi, atoms, marking, costs):
    idx = {a: i for i, a in enumerate(atoms)}
    dirty = [idx[a] for a in atoms if marking[a] == Z]
    v = lean_fun([(idx[a], "V.T" if marking[a] == T else "V.F") for a in atoms if marking[a] != Z], "V.Z")
    c = lean_fun([(idx[a], costs[a]) for a in atoms], "0")
    return lean_fm(phi, idx), v, c, dirty


def run_lean(lines, prefix):
    fd, path = tempfile.mkstemp(prefix=prefix, suffix=".lean", dir=LEAN)
    with os.fdopen(fd, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")
    try:
        return subprocess.run(["lake", "env", "lean", path], cwd=LEAN, capture_output=True, text=True, timeout=1800)
    finally:
        os.unlink(path)


def kernel(cs, py):
    """Lean's `opt` for every case (evaluated), and the small ones stated as theorems with Python's number.
    -> (numbers, how many were stated as theorems)"""
    lines = ["import ZPlan", "open V ZPlan", ""]
    stated = 0
    for k, (phi, atoms, marking, costs) in enumerate(cs):
        fm, v, c, dirty = lean_terms(phi, atoms, marking, costs)
        lines += [f"def f{k} : Fm := {fm}", f"def v{k} : Nat → V := {v}", f"def c{k} : Nat → Nat := {c}",
                  f'#eval IO.println s!"J{k} {{opt c{k} f{k} {len(dirty)} {dirty} v{k}}}"']
        if len(dirty) <= DECIDE_UP_TO and stated < DECIDE_AT_MOST:
            lines.append(f"example : opt c{k} f{k} {len(dirty)} {dirty} v{k} = {py[k]} := by decide")
            stated += 1
    r = run_lean(lines, "zplan_bridge_")
    if r.returncode != 0:
        raise SystemExit("LEAN FAILED:\n" + (r.stdout + r.stderr)[-3000:])
    res = {}
    for l in r.stdout.splitlines():
        if l.startswith("J"):
            head, rest = l.split(" ", 1)
            res[int(head[1:])] = int(rest)
    return [res[k] for k in range(len(cs))], stated


def python_cost(phi, atoms, marking, costs):
    r = zplan.plan(phi, marking, costs)
    if "refused" in r or "no_plan" in r:
        raise SystemExit(f"zplan gave no plan where every dirty ground can be checked: {r}")
    return 0 if r["already"] else int(r["worst_case"]["cost"])


def main():
    cs = cases()
    py = [python_cost(*c) for c in cs]
    got, stated = kernel(cs, py)
    bad = [(k, py[k], got[k]) for k in range(len(cs)) if py[k] != got[k]]
    open_cases = sum(1 for x in got if x > 0)
    print(f"cases: {len(cs)}; not settled at the start: {open_cases}; Python = Lean `opt`: {len(cs) - len(bad)} of {len(cs)}; "
          f"also stated as theorems and accepted by the kernel: {stated}")
    for b in bad[:5]:
        print("  DIFFERS: case %d, Python %d, Lean %d" % b)

    # MUTATION 1: the sabotaged module must differ from Lean somewhere
    zplan.MUTANT["best_branch"] = True
    try:
        mut = [python_cost(*c) for c in cs]
    finally:
        zplan.MUTANT.clear()
    caught = sum(1 for k in range(len(cs)) if mut[k] != got[k])
    print(f"MUTATION (the better branch taken for the worse): differs from Lean on {caught} cases - "
          f"{'caught' if caught else 'NOT SEEN'}")

    # MUTATION 2: a wrong number stated as a theorem - the kernel must refuse
    k0 = next(k for k, c in enumerate(cs) if got[k] > 0 and len(lean_terms(*c)[3]) <= DECIDE_UP_TO)
    fm, v, c, dirty = lean_terms(*cs[k0])
    wrong = ["import ZPlan", "open V ZPlan", "",
             f"example : opt ({c}) {fm} {len(dirty)} {dirty} ({v}) = {got[k0] - 1} := by decide"]
    right = wrong[:3] + [wrong[3].replace(f"= {got[k0] - 1} := by decide", f"= {got[k0]} := by decide")]
    r_wrong, r_right = run_lean(wrong, "zplan_wrong_"), run_lean(right, "zplan_right_")
    refused = r_wrong.returncode != 0 and r_right.returncode == 0
    print(f"a wrong number as a theorem (case {k0}: {got[k0] - 1} for {got[k0]}): "
          f"{'the kernel refuses; the right one it accepts' if refused else 'NOT REFUSED'}")

    ok = not bad and caught > 0 and refused and open_cases > 200 and stated > 20
    print("ZPLAN LEAN BRIDGE GREEN" if ok else "ZPLAN LEAN BRIDGE RED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
