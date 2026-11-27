# -*- coding: utf-8 -*-
"""
zpassport ↔ lean/ZStipulate.lean — the stipulation theorem, from MEASURED to PROVED (2026-11-27).

`zpassport.stipulation_theorem` measured it on zoos: an UNDERDETERMINED / INTRINSIC component, once one of its classical
models is stipulated, is grounded at that model and nothing already grounded moves. `lean/ZStipulate.lean` proves it
(`V.stipulation`, no axioms) for any system and any model M above the least fixed point whose stipulated definitions
evaluate to the stipulated values.

This stand ties the passport to the theorem. On the passport's zoos (MIXED, RUSSELL), on cycles, and on seeded random
systems, for every component the passport calls UNDERDETERMINED or INTRINSIC and every model it lists:
  1. the theorem's HYPOTHESES hold, computed by the kernel: M = the least fixed point with the component overwritten by
     the model lies above lfp d, and every stipulated definition evaluates (`evalS M`) to the stipulated value — so the
     theorem covers that case;
  2. the Python stipulated fixed point (`least_fp_stable(stipulate(system, m))`) equals the kernel's `lfp (stip d σ)`.
Inputs ("m": "Z") are foreign atoms on the Lean side, numbered after the own names.
MUTATION: a model with one value flipped -> hypothesis 1 fails in the kernel (a non-model is not covered).

Run:  python3 inventory/zpassport_lean_bridge.py   -> ZPASSPORT LEAN BRIDGE GREEN
"""
import os
import random
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
import zpassport as P                  # noqa: E402
from fixedpoint import least_fp_stable, N     # noqa: E402
from ztl import T, F, Z                # noqa: E402

LEAN = os.path.join(ROOT, "lean")
OPS = {"and": "conj", "or": "disj", "imp": "imp", "xor": "xor", "xnor": "xnor"}


def encode(system):
    own = [s for s in system if system[s] != Z]
    inputs = [s for s in system if system[s] == Z]
    index = {s: i for i, s in enumerate(own + inputs)}

    def fm(phi):
        if phi == "T":
            return "(.top)"
        if phi == "F":
            return "(.bot)"
        if isinstance(phi, str):
            return f"(.atom {index[phi]})"
        if phi[0] == "not":
            return f"(.neg {fm(phi[1])})"
        return f"(.{OPS[phi[0]]} {fm(phi[1])} {fm(phi[2])})"
    return own, "[" + ", ".join(fm(system[s]) for s in own) + "]"


def ph(x):
    return {T: ".t", F: ".f", N: ".n"}[x]


def gen(rnd, names, depth=2):
    if depth == 0 or rnd.random() < 0.3:
        return rnd.choice(names)
    if rnd.random() < 0.25:
        return ("not", gen(rnd, names, depth - 1))
    return (rnd.choice(list(OPS)), gen(rnd, names, depth - 1), gen(rnd, names, depth - 1))


def systems():
    out = [("MIXED", P.MIXED), ("RUSSELL", P.RUSSELL)]
    for pat in ([True], [False], [False, False], [True, False], [True, True], [False, False, True], [True, True, True, True]):
        out.append((f"cycle {pat}", P.cycle_system(pat)))
    rnd = random.Random(20261127)
    for i in range(120):
        n = rnd.randint(1, 5)
        names = [f"s{j}" for j in range(n)]
        sysd = {s: gen(rnd, names) for s in names}
        if rnd.random() < 0.3:
            sysd["inp"] = Z
            sysd[names[0]] = ("or", sysd[names[0]], "inp")
        out.append((f"random {i}", sysd))
    return out


def main():
    jobs = []      # (label, own, lean_sys, sigma, M, expected_lfp2)
    for label, system in systems():
        lfp, reports, _ = P.passports(system)
        own, lsys = encode(system)
        for comp, kind, _ in reports:
            if kind not in ("UNDERDETERMINED", "INTRINSIC"):
                continue
            names = set(comp)
            env_names = set()
            for s in comp:
                env_names |= P.deps(system[s]) - names
            env = {n: lfp[n] for n in env_names}
            for m in P.component_models(comp, system, env):
                lfp2 = least_fp_stable(P.stipulate(system, m))
                sigma = [(f"some {'true' if m[s] == T else 'false'}" if s in m else "none") for s in own]
                M = [ph(m[s]) if s in m else ph(lfp[s]) for s in own]
                jobs.append((label, own, lsys, sigma, M, [ph(lfp2[s]) for s in own]))
    mut = None
    for j in jobs:
        if any(x != "none" for x in j[3]):
            k = next(i for i, x in enumerate(j[3]) if x != "none")
            sigma = list(j[3]); M = list(j[4])
            flip = "some false" if sigma[k] == "some true" else "some true"
            sigma[k] = flip; M[k] = ".f" if flip == "some false" else ".t"
            mut = (j[0] + " MUTATED", j[1], j[2], sigma, M, j[5])
            break
    lines = ["import ZStipulate", "open V", ""]
    allj = jobs + ([mut] if mut else [])
    for k, (label, own, lsys, sigma, M, exp) in enumerate(allj):
        n = len(own)
        lines.append(f"def d{k} : Sys := {lsys}")
        lines.append(f"def s{k} : List (Option Bool) := [{', '.join(sigma)}]")
        lines.append(f"def m{k} : PVal := [{', '.join(M)}]")
        hyp = (f"pvLeq (lfp d{k}) m{k} && (List.range {n}).all (fun i => match getO s{k} i with "
               f"| some b => evalS m{k} (getF d{k} i) == ph b | none => true)")
        lines.append(f'#eval IO.println s!"K{k} {{{hyp}}} {{lfp (stip d{k} s{k}) == [{", ".join(exp)}]}}"')
    fd, path = tempfile.mkstemp(prefix="zpassport_bridge_", suffix=".lean", dir=LEAN)
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
            k, a, b = l.split()
            got[int(k[1:])] = (a == "true", b == "true")
    hyp_ok = sum(got[k][0] for k in range(len(jobs)))
    lfp_ok = sum(got[k][1] for k in range(len(jobs)))
    kinds = {}
    for label, system in systems():
        for _, kind, _ in P.passports(system)[1]:
            kinds[kind] = kinds.get(kind, 0) + 1
    print(f"systems {len(systems())}; passport kinds {dict(sorted(kinds.items()))}")
    print(f"models stipulated {len(jobs)}: theorem's hypotheses hold {hyp_ok}/{len(jobs)}, "
          f"Python stipulated lfp == kernel {lfp_ok}/{len(jobs)}")
    caught = mut is not None and not got[len(jobs)][0]
    print(f"mutation (one model value flipped): {'caught — hypothesis fails' if caught else 'NOT CAUGHT'}")
    if hyp_ok == lfp_ok == len(jobs) and len(jobs) > 0 and caught:
        print("ZPASSPORT LEAN BRIDGE GREEN")
    else:
        for k in range(len(jobs)):
            if not all(got[k]):
                print("  DIFF", jobs[k][0], jobs[k][3], jobs[k][4], got[k])
        print("ZPASSPORT LEAN BRIDGE RED"); sys.exit(1)


if __name__ == "__main__":
    main()
