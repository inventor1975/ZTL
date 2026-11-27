# -*- coding: utf-8 -*-
"""
zfl.cyclic_stable ↔ lean/ZInputSubst.lean — per-occurrence inputs vs identified inputs (2026-11-27).

`lean/ZInputSubst.lean` proves (`V.lfp_subst_mono`, no axioms): substituting the INPUTS of a system, own names kept,
never revokes a grounding. `zfl.cyclic_stable` relies on two instances: identifying the per-occurrence copies of a
repeated dirty input, and fixing an input to T or F (a completion). This stand checks, on seeded random self-referential
systems with a repeated input:
  1. Python's stable least fixed point (`fixedpoint.least_fp_stable`) equals the kernel's `lfp` on the per-occurrence
     system, on the identified one, and on both completions;
  2. the kernel confirms the theorem's conclusion on each instance (per-occurrence ≤ identified ≤ each completion is the
     theorem's direction; it is printed, not assumed);
  3. the strict cases exist: some names grounded only after identification (the reason cyclic_stable exists), so the
     battery is not vacuous.
MUTATION: a per-occurrence value forced to the opposite of the identified one -> the order check fails.

Run:  python3 inventory/zinputsubst_lean_bridge.py   -> ZINPUTSUBST LEAN BRIDGE GREEN
"""
import os
import random
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
from fixedpoint import least_fp_stable, N     # noqa: E402
from ztl import T, F, Z                # noqa: E402

LEAN = os.path.join(ROOT, "lean")
OPS = {"and": "conj", "or": "disj", "imp": "imp", "xor": "xor", "xnor": "xnor"}


def gen(rnd, names, depth):
    if depth == 0 or rnd.random() < 0.3:
        return rnd.choice(names)
    if rnd.random() < 0.25:
        return ("not", gen(rnd, names, depth - 1))
    return (rnd.choice(list(OPS)), gen(rnd, names, depth - 1), gen(rnd, names, depth - 1))


def split(phi, counter):
    """every occurrence of the input x becomes its own input x__occK"""
    if phi == "x":
        counter[0] += 1
        return f"x__occ{counter[0]}"
    if isinstance(phi, str):
        return phi
    return (phi[0],) + tuple(split(p, counter) for p in phi[1:])


def fix(phi, val):
    if phi == "x":
        return val
    if isinstance(phi, str):
        return phi
    return (phi[0],) + tuple(fix(p, val) for p in phi[1:])


def fm(phi, index):
    if phi == "T":
        return "(.top)"
    if phi == "F":
        return "(.bot)"
    if isinstance(phi, str):
        return f"(.atom {index[phi]})"
    if phi[0] == "not":
        return f"(.neg {fm(phi[1], index)})"
    return f"(.{OPS[phi[0]]} {fm(phi[1], index)} {fm(phi[2], index)})"


def count(phi, name):
    if isinstance(phi, str):
        return int(phi == name)
    return sum(count(p, name) for p in phi[1:])


def ph(x):
    return {T: "t", F: "f", N: "n"}[x]


def main():
    rnd = random.Random(20261127)
    cases = []
    while len(cases) < 150:
        n = rnd.randint(1, 3)
        own = [f"s{j}" for j in range(n)]
        system = {s: gen(rnd, own + ["x"], 3) for s in own}
        if sum(count(system[s], "x") for s in own) < 2:
            continue
        if not any(count(system[s], t) for s in own for t in own):
            continue                                       # self-referential only (cyclic_stable's case)
        c = [0]
        sp = {s: split(system[s], c) for s in own}
        occs = [f"x__occ{k}" for k in range(1, c[0] + 1)]
        cases.append((own, system, sp, occs))
    lines = ["import ZInputSubst", "open V", "",
             "def phs : List Ph → String | [] => \"\" | p :: r => (match p with | .t => \"t\" | .f => \"f\" | .n => \"n\") ++ phs r"]
    expect = []
    strict = 0
    for k, (own, system, sp, occs) in enumerate(cases):
        n = len(own)
        idx_sp = {s: i for i, s in enumerate(own + occs)}
        idx_id = {s: i for i, s in enumerate(own + ["x"])}
        dsp = "[" + ", ".join(fm(sp[s], idx_sp) for s in own) + "]"
        did = "[" + ", ".join(fm(system[s], idx_id) for s in own) + "]"
        tau = " ".join(f"| {idx_sp[o]} => .atom {n}" for o in occs)
        lines.append(f"def sp{k} : Sys := {dsp}")
        lines.append(f"def id{k} : Sys := {did}")
        lines.append(f"def tau{k} : Nat → Fm := fun m => match m with {tau} | j => .atom j")
        for v, nm in ((T, "T"), (F, "F")):
            dfx = "[" + ", ".join(fm(fix(system[s], nm), idx_id) for s in own) + "]"
            lines.append(f"def fx{nm}{k} : Sys := {dfx}")
        lines.append(f'#eval IO.println s!"K{k} {{phs (lfp sp{k})}} {{phs (lfp id{k})}} {{phs (lfp fxT{k})}} '
                     f'{{phs (lfp fxF{k})}} {{pvLeq (lfp sp{k}) (lfp (sp{k}.map (substF tau{k}))) && '
                     f'(lfp (sp{k}.map (substF tau{k})) == lfp id{k}) && pvLeq (lfp id{k}) (lfp fxT{k}) && '
                     f'pvLeq (lfp id{k}) (lfp fxF{k})}}"')
        sys_sp = {**{s: sp[s] for s in own}, **{o: Z for o in occs}}
        sys_id = {**{s: system[s] for s in own}, "x": Z}
        py = []
        for sysd in (sys_sp, sys_id, {s: fix(system[s], "T") for s in own}, {s: fix(system[s], "F") for s in own}):
            l = least_fp_stable(sysd)
            py.append("".join(ph(l[s]) for s in own))
        expect.append(py)
        strict += any(a == "n" and b != "n" for a, b in zip(py[0], py[1]))
    fd, path = tempfile.mkstemp(prefix="zinputsubst_bridge_", suffix=".lean", dir=LEAN)
    with os.fdopen(fd, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")
    try:
        r = subprocess.run(["lake", "env", "lean", path], cwd=LEAN, capture_output=True, text=True, timeout=1800)
    finally:
        os.unlink(path)
    if r.returncode != 0:
        raise SystemExit("LEAN FAILED:\n" + (r.stdout + r.stderr)[-3000:])
    got = {}
    for l in r.stdout.splitlines():
        if l.startswith("K"):
            parts = l.split()
            got[int(parts[0][1:])] = parts[1:]
    eq = sum(got[k][:4] == expect[k] for k in range(len(cases)))
    order = sum(got[k][4] == "true" for k in range(len(cases)))
    print(f"systems {len(cases)}: Python lfp == kernel (per-occurrence, identified, both completions) {eq}/{len(cases)}; "
          f"theorem's order holds {order}/{len(cases)}; grounded only after identification: {strict}")
    # MUTATION: claim the per-occurrence system grounds a name the identified one gives the opposite value
    k0 = next(k for k in range(len(cases)) if "t" in expect[k][1] or "f" in expect[k][1])
    i0 = next(i for i, c in enumerate(expect[k0][1]) if c in "tf")
    fake = list(expect[k0][1]); fake[i0] = "f" if fake[i0] == "t" else "t"
    caught = not all((a == "n") or (a == b) for a, b in zip(fake, expect[k0][1]))
    print(f"mutation (a per-occurrence value opposite to the identified one): {'caught' if caught else 'NOT CAUGHT'}")
    if eq == order == len(cases) and strict > 0 and caught:
        print("ZINPUTSUBST LEAN BRIDGE GREEN")
    else:
        for k in range(len(cases)):
            if got[k][:4] != expect[k] or got[k][4] != "true":
                print("  DIFF", cases[k][1], expect[k], got[k]); break
        print("ZINPUTSUBST LEAN BRIDGE RED"); sys.exit(1)


if __name__ == "__main__":
    main()
