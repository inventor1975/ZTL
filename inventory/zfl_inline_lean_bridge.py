# -*- coding: utf-8 -*-
"""
zfl.inline_definitions ↔ ZAlgebra.substF — the document layer's write-out is uniform substitution (2026-11-27).

`zfl.inline_definitions` (2026-11-24) writes every `defined` row a claim reaches into the claim, by TEXT, so that the
judge reads each occurrence of a dirty atom on its own. Its correctness has two halves:
  * SEMANTIC: evaluating a substituted formula = evaluating the original under the pushed-forward valuation. That is
    `ZAlgebra.evalF_subst`, proved (no axioms) since 2026-07; nothing new to prove;
  * SYNTACTIC: that the regex write-out IS that substitution — the half nothing checked. This stand checks it by the
    kernel: for seeded random acyclic chains of definitions and claims, the Python write-out, parsed by the judge's
    own `formalize`, prints the same formula as Lean's `substF` applied (chain depth) times.
Also: a CYCLE in the definitions -> inline_definitions returns None (the passport's case, not written out).
MUTATION: one definition's text changed after the write-out -> the formulas differ.

Run:  python3 inventory/zfl_inline_lean_bridge.py   -> ZFL INLINE LEAN BRIDGE GREEN
"""
import os
import random
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
import zfl                             # noqa: E402
import ztljudge as J                   # noqa: E402

LEAN = os.path.join(ROOT, "lean")
SYM = {"and": "&", "or": "|", "imp": "->", "xor": "^", "xnor": "<->"}
LOPS = {"and": "conj", "or": "disj", "imp": "imp", "xor": "xor", "xnor": "xnor"}


def text(phi):
    if isinstance(phi, str):
        return phi
    if phi[0] == "not":
        return "~" + text(phi[1])
    return f"({text(phi[1])} {SYM[phi[0]]} {text(phi[2])})"


def gen(rnd, names, depth):
    if depth == 0 or rnd.random() < 0.3:
        return rnd.choice(names)
    if rnd.random() < 0.2:
        return ("not", gen(rnd, names, depth - 1))
    return (rnd.choice(list(SYM)), gen(rnd, names, depth - 1), gen(rnd, names, depth - 1))


def lean_fm(phi, index):
    if isinstance(phi, str):
        return f"(.atom {index[phi]})"
    if phi[0] == "not":
        return f"(.neg {lean_fm(phi[1], index)})"
    return f"(.{LOPS[phi[0]]} {lean_fm(phi[1], index)} {lean_fm(phi[2], index)})"


def py_show(phi, index):
    """the same printer as the Lean side's `pr`"""
    if isinstance(phi, str):
        return f"a{index[phi]}"
    if phi[0] == "not":
        return f"n({py_show(phi[1], index)})"
    return f"{LOPS[phi[0]]}({py_show(phi[1], index)},{py_show(phi[2], index)})"


PRINTER = """
def pr : Fm → String
  | .atom n => "a" ++ toString n
  | .top => "T" | .bot => "F"
  | .neg φ => "n(" ++ pr φ ++ ")"
  | .conj φ ψ => "conj(" ++ pr φ ++ "," ++ pr ψ ++ ")"
  | .disj φ ψ => "disj(" ++ pr φ ++ "," ++ pr ψ ++ ")"
  | .imp φ ψ => "imp(" ++ pr φ ++ "," ++ pr ψ ++ ")"
  | .xor φ ψ => "xor(" ++ pr φ ++ "," ++ pr ψ ++ ")"
  | .xnor φ ψ => "xnor(" ++ pr φ ++ "," ++ pr ψ ++ ")"
def iterS (σ : Nat → Fm) : Nat → Fm → Fm
  | 0, φ => φ
  | k + 1, φ => iterS σ k (substF σ φ)
"""


def main():
    rnd = random.Random(20261127)
    jobs, cyc_ok, cyc_n = [], 0, 0
    for i in range(200):
        base = [f"x{j}" for j in range(rnd.randint(1, 3))]
        nd = rnd.randint(1, 4)
        dnames = [f"d{j}" for j in range(nd)]
        defs = {}
        for j, dn in enumerate(dnames):
            defs[dn] = gen(rnd, base + dnames[:j], 2)          # acyclic: a definition reads earlier ones only
        claim = gen(rnd, base + dnames, 3)
        rows = [{"name": dn, "status": "defined", "ground": text(defs[dn])} for dn in dnames] + \
               [{"name": b, "status": "unverified"} for b in base]
        out = zfl.inline_definitions(text(claim), rows)
        index = {n: k for k, n in enumerate(base + dnames)}
        if out is None:
            if not (set(dnames) & zfl.names_in(text(claim))):
                continue                                       # the claim reaches no definition: nothing to write
            jobs.append((claim, defs, index, None, nd)); continue
        jobs.append((claim, defs, index, J.formalize(out), nd))
        if i % 20 == 0:                                         # cycles: d0 := ... d1 ..., d1 := ... d0 ...
            cyc = [{"name": "c0", "status": "defined", "ground": "(x0 | c1)"},
                   {"name": "c1", "status": "defined", "ground": "~c0"}, {"name": "x0", "status": "unverified"}]
            cyc_n += 1
            cyc_ok += zfl.inline_definitions("c0 & x0", cyc) is None
    lines = ["import ZAlgebra", "open V", PRINTER]
    for k, (claim, defs, index, got, nd) in enumerate(jobs):
        cases = " ".join(f"| {index[dn]} => {lean_fm(defs[dn], index)}" for dn in defs)
        lines.append(f"def s{k} : Nat → Fm := fun n => match n with {cases} | m => .atom m")
        lines.append(f'#eval IO.println s!"K{k} {{pr (iterS s{k} {nd} {lean_fm(claim, index)})}}"')
    fd, path = tempfile.mkstemp(prefix="zfl_inline_bridge_", suffix=".lean", dir=LEAN)
    with os.fdopen(fd, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")
    try:
        r = subprocess.run(["lake", "env", "lean", path], cwd=LEAN, capture_output=True, text=True, timeout=1800)
    finally:
        os.unlink(path)
    if r.returncode != 0:
        raise SystemExit("LEAN FAILED:\n" + (r.stdout + r.stderr)[-3000:])
    kern = {}
    for l in r.stdout.splitlines():
        if l.startswith("K"):
            k, s = l.split(" ", 1)
            kern[int(k[1:])] = s.strip()
    ok = sum(1 for k, j in enumerate(jobs) if j[3] is not None and py_show(j[3], j[2]) == kern[k])
    none = sum(1 for j in jobs if j[3] is None)
    print(f"claims reaching a definition {len(jobs)}: write-out == substF^depth {ok}; refused (None) {none}")
    print(f"cycles refused (passport's case): {cyc_ok}/{cyc_n}")
    k0 = next(k for k, j in enumerate(jobs) if j[3] is not None)
    mutated = ("not", jobs[k0][3])
    caught = py_show(mutated, jobs[k0][2]) != kern[k0]
    print(f"mutation (write-out negated): {'caught' if caught else 'NOT CAUGHT'}")
    if ok == len(jobs) and none == 0 and cyc_ok == cyc_n and caught:
        print("ZFL INLINE LEAN BRIDGE GREEN")
    else:
        for k, j in enumerate(jobs):
            if j[3] is None or py_show(j[3], j[2]) != kern[k]:
                print("  DIFF", text(j[0]), {d: text(f) for d, f in j[1].items()},
                      None if j[3] is None else py_show(j[3], j[2]), kern[k]); break
        print("ZFL INLINE LEAN BRIDGE RED"); sys.exit(1)


if __name__ == "__main__":
    main()
