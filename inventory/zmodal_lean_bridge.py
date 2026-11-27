# -*- coding: utf-8 -*-
"""
zmodal ↔ ZGround.evalS — the modal layer IS the stable step (2026-11-27).

`zmodal.global_super` (used by `zverify`) reads a formula over the classical completions of a marking: T when it holds
in every completion (□), F when in none (¬◇), else the super-gap. `ZGround.evalS` — the stable step, a definition the
kernel proves monotone and grounds the passport with — is the same three-way reading over the completions of a phase
list (T→t, F→f, unverified→n). This stand makes the identity a checked fact: on seeded random formulas and markings,
the kernel's `evalS` equals `global_super` (t↔T, f↔F, n↔Z). Also `box`/`dia` duality: dia φ == not box ¬φ.
MUTATION: one marking's checked atom flipped on the Python side -> a difference appears.

Run:  python3 inventory/zmodal_lean_bridge.py   -> ZMODAL LEAN BRIDGE GREEN
"""
import os
import random
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
import zmodal as M                     # noqa: E402
from ztl import T, F, Z                # noqa: E402

LEAN = os.path.join(ROOT, "lean")
OPS = {"and": "conj", "or": "disj", "imp": "imp", "xor": "xor", "xnor": "xnor"}


def gen(rnd, names, depth):
    if depth == 0 or rnd.random() < 0.3:
        return rnd.choice(names)
    if rnd.random() < 0.25:
        return ("not", gen(rnd, names, depth - 1))
    return (rnd.choice(list(OPS)), gen(rnd, names, depth - 1), gen(rnd, names, depth - 1))


def fm(phi, idx):
    if isinstance(phi, str):
        return f"(.atom {idx[phi]})"
    if phi[0] == "not":
        return f"(.neg {fm(phi[1], idx)})"
    return f"(.{OPS[phi[0]]} {fm(phi[1], idx)} {fm(phi[2], idx)})"


def main():
    rnd = random.Random(20261127)
    cases = []
    for _ in range(400):
        names = [f"a{j}" for j in range(rnd.randint(1, 4))]
        phi = gen(rnd, names, 3)
        marked = {n: rnd.choice([T, F, "M"]) for n in names}
        cases.append((names, phi, marked))
    lines = ["import ZGround", "open V", "",
             'def phs : Ph → String | .t => "t" | .f => "f" | .n => "n"']
    for k, (names, phi, marked) in enumerate(cases):
        idx = {n: i for i, n in enumerate(names)}
        pv = "[" + ", ".join({T: ".t", F: ".f"}.get(marked[n], ".n") for n in names) + "]"
        lines.append(f'#eval IO.println s!"K{k} {{phs (evalS {pv} {fm(phi, idx)})}}"')
    fd, path = tempfile.mkstemp(prefix="zmodal_bridge_", suffix=".lean", dir=LEAN)
    with os.fdopen(fd, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")
    try:
        r = subprocess.run(["lake", "env", "lean", path], cwd=LEAN, capture_output=True, text=True, timeout=1800)
    finally:
        os.unlink(path)
    if r.returncode != 0:
        raise SystemExit("LEAN FAILED:\n" + (r.stdout + r.stderr)[-3000:])
    kern = {int(l.split()[0][1:]): l.split()[1] for l in r.stdout.splitlines() if l.startswith("K")}
    want = {T: "t", F: "f", Z: "n"}
    ok = sum(want[M.global_super(phi, marked)] == kern[k] for k, (_, phi, marked) in enumerate(cases))
    dual = sum(M.dia(phi, marked) == (not M.box(("not", phi), marked)) for _, phi, marked in cases)
    dist = {v: sum(1 for x in kern.values() if x == v) for v in "tfn"}
    print(f"cases {len(cases)}: global_super == kernel evalS {ok}/{len(cases)} (kernel t/f/n: {dist}); "
          f"◇ = ¬□¬ {dual}/{len(cases)}")
    caught = False                       # the first case where changing one atom's mark changes the verdict
    for k, (names, phi, marked) in enumerate(cases):
        for a in names:
            for v in (T, F, "M"):
                if v != marked[a] and want[M.global_super(phi, {**marked, a: v})] != kern[k]:
                    caught = True
                    break
            if caught:
                break
        if caught:
            break
    print(f"mutation (one atom's mark changed on the Python side): {'caught' if caught else 'NOT CAUGHT'}")
    if ok == dual == len(cases) and caught and min(dist.values()) > 0:
        print("ZMODAL LEAN BRIDGE GREEN")
    else:
        print("ZMODAL LEAN BRIDGE RED"); sys.exit(1)


if __name__ == "__main__":
    main()
