# -*- coding: utf-8 -*-
"""
znaive ↔ lean/ZGround.lean — naive set universes, their grounding computed by the kernel (2026-11-27).

`znaive` turns naive set definitions (lists, given cells, {x : φ} with self-reference allowed) into a fixedpoint
system — one sentence per cell a∈S — and grounds it with the stable least fixed point (`fixedpoint.least_fp_stable`),
then the passport. Two checks tie it:
  * the TRANSLATION is checked against an independent evaluator by `znaive.oracle_check` (its own stand: every
    classical model of the system, the inputs read freely, agrees with the lfp where the lfp decides);
  * the GROUNDING, here: on seeded random universes the system znaive builds is sent to the kernel, and Python's lfp
    must equal `ZGround.lfp` cell by cell — with every passport STIPULATION (UNDERDETERMINED / INTRINSIC models)
    covered by `ZStipulate.stipulation` through inventory/zpassport_lean_bridge.py's encoding.
Given cells "Z" are inputs: foreign atoms on the Lean side. MUTATION: one cell's lfp value flipped on the Python side
-> a difference.

Run:  python3 inventory/znaive_lean_bridge.py   -> ZNAIVE LEAN BRIDGE GREEN
"""
import os
import random
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
sys.path.insert(0, HERE)
import znaive                          # noqa: E402
from fixedpoint import N               # noqa: E402
from ztl import T, F, Z                # noqa: E402
import importlib.util                  # noqa: E402

_spec = importlib.util.spec_from_file_location("zpb", os.path.join(HERE, "zpassport_lean_bridge.py"))
zpb = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(zpb)
LEAN = os.path.join(ROOT, "lean")


def main():
    rng = random.Random(20261127)
    cases = []
    while len(cases) < 120:
        spec = znaive._rand_universe(rng)
        try:
            u, sysm, lfp, kind = znaive.analyse(spec)
        except znaive.UniverseError:
            continue
        own, lsys = zpb.encode(sysm)
        cases.append((own, lsys, "".join({T: "t", F: "f", N: "n"}[lfp[c]] for c in own), kind))
    lines = ["import ZGround", "open V", "",
             'def phs : List Ph → String | [] => "" | p :: r => (match p with | .t => "t" | .f => "f" | .n => "n") ++ phs r']
    for k, (own, lsys, want, _) in enumerate(cases):
        lines.append(f'#eval IO.println s!"K{k} {{phs (lfp {lsys})}}"')
    fd, path = tempfile.mkstemp(prefix="znaive_bridge_", suffix=".lean", dir=LEAN)
    with os.fdopen(fd, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")
    try:
        r = subprocess.run(["lake", "env", "lean", path], cwd=LEAN, capture_output=True, text=True, timeout=1800)
    finally:
        os.unlink(path)
    if r.returncode != 0:
        raise SystemExit("LEAN FAILED:\n" + (r.stdout + r.stderr)[-3000:])
    got = {int(l.split()[0][1:]): (l.split()[1] if len(l.split()) > 1 else "") for l in r.stdout.splitlines()
           if l.startswith("K")}
    ok = sum(got[k] == c[2] for k, c in enumerate(cases))
    kinds = {}
    for c in cases:
        for v in c[3].values():
            kinds[v] = kinds.get(v, 0) + 1
    cells = sum(len(c[0]) for c in cases)
    print(f"universes {len(cases)} ({cells} cells; kinds {dict(sorted(kinds.items()))}): Python lfp == kernel lfp "
          f"{ok}/{len(cases)}")
    k0 = next(k for k, c in enumerate(cases) if any(ch in "tf" for ch in c[2]))
    w = cases[k0][2]; i = next(j for j, ch in enumerate(w) if ch in "tf")
    fake = w[:i] + ("f" if w[i] == "t" else "t") + w[i + 1:]
    caught = fake != got[k0]
    print(f"mutation (one grounded cell flipped): {'caught' if caught else 'NOT CAUGHT'}")
    if ok == len(cases) and caught and kinds.get("PARADOX", 0) > 0 and kinds.get("GROUNDED", 0) > 0:
        print("ZNAIVE LEAN BRIDGE GREEN")
    else:
        print("ZNAIVE LEAN BRIDGE RED"); sys.exit(1)


if __name__ == "__main__":
    main()
