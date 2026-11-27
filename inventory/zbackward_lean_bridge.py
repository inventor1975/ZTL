# -*- coding: utf-8 -*-
"""
zbackward ↔ lean/ZBackward.lean — the backward pass against its definition, computed by the kernel (2026-11-27).

The curator: «каждая его деталь — теорема… пройдёмся, проверим». `lean/ZBackward.lean` proves, with no axioms, what
the family of minimal sets IS (`fam`: sound, an antichain, complete — every set with the property contains a member,
`exists_minimal`; already reached ⇒ exactly {∅}). This stand ties the Python answer to that definition:

  for seeded random claims, markings and targets, the JUDGE is asked once per world (every ground filled T/F or left
  dirty — the 3^n worlds), the worlds that hit the target are written into a Lean file as a table, and the kernel
  evaluates `fam (possibleB table)` and `fam (guaranteedB table)`. The families must equal `zbackward.backward`'s, by
  BOTH of its routes: the tables (`zbackward_tree`, default) and the size-ascending enumeration (`use_tree=False`).
  "already" must hold exactly when the kernel's family is {∅}.

The oracle is the Python judge on both sides, by design: the theorems are about the search, for ANY oracle; that the
oracle is the judge is the other bridges' business (bridge.py, test_zjudge2lean.py).

Enumeration route: compared where it is not cut (n ≤ zbackward.MAX_K); for n > MAX_K its sets of size ≤ MAX_K must be
exactly the kernel's sets of that size, and its empty flags None ("not searched"), never True.

NEXT CHECK (`ztljudge.next_check`, the judge's "check this next"): on every case whose target is "settled" (EARNED or
REFUTED) and not already reached, it must return a SETTLING atom exactly when the kernel's guaranteed family has a
singleton, and that singleton must be its atom; otherwise, a PARTIAL atom (one outcome terminal) exactly when the
kernel's possible family has a singleton. So the judge's own "what to check" is the backward pass restricted to size 1.

MUTATION: one set dropped from a Python family -> the comparison must call it a difference.

Run:  python3 inventory/zbackward_lean_bridge.py   -> ZBACKWARD LEAN BRIDGE GREEN
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
from ztl import T, F, Z                # noqa: E402

LEAN = os.path.join(ROOT, "lean")
OPS = ["and", "or", "imp", "xor", "xnor"]
TARGETS = [("EARNED", True), ("REFUTED", True), ("ON CREDIT", True), ("OPEN", True), (ZB.TERMINAL, True),
           (T, False), (F, False)]


def gen(rnd, leaves):
    if len(leaves) == 1:
        return ("not", leaves[0]) if rnd.random() < 0.2 else leaves[0]
    k = rnd.randint(1, len(leaves) - 1)
    node = (rnd.choice(OPS), gen(rnd, leaves[:k]), gen(rnd, leaves[k:]))
    return ("not", node) if rnd.random() < 0.15 else node


def cases(seed=20261127, n_cases=600):
    rnd = random.Random(seed)
    out = []
    for i in range(n_cases):
        n_atoms = rnd.randint(2, 6)
        atoms = [f"a{j}" for j in range(n_atoms)]
        leaves = atoms + ([rnd.choice(atoms)] if rnd.random() < 0.35 else [])      # some grounds repeated
        rnd.shuffle(leaves)
        phi = gen(rnd, leaves)
        marking = {a: rnd.choice([Z, Z, Z, T, F]) for a in atoms}
        grounds = tuple(a for a, v in sorted(marking.items()) if v == Z)
        if not 1 <= len(grounds) <= 5:
            continue
        target, by_disp = TARGETS[i % len(TARGETS)]
        out.append((phi, marking, grounds, target, by_disp))
    return out


def table(phi, marking, grounds, target, by_disp):
    """the worlds (one entry per ground: None dirty, True/False filled) where the judge hits the target"""
    hit = []
    for w in itertools.product((None, False, True), repeat=len(grounds)):
        m = dict(marking)
        for g, x in zip(grounds, w):
            m[g] = Z if x is None else (T if x else F)
        if ZB._hits(ZB._outcome(phi, m, by_disp), target):
            hit.append(w)
    return hit


def lean_world(w):
    return "[" + ", ".join("none" if x is None else f"some {'true' if x else 'false'}" for x in w) + "]"


def as_idx(family, grounds):
    return sorted(sorted(grounds.index(g) for g in S) for S in family)


def kernel(jobs):
    """jobs: (n, hit-table). Returns, per job, (possible family, guaranteed family) as sorted index lists."""
    lines = ["import ZBackward", "open ZBackward", ""]
    for k, (n, hit) in enumerate(jobs):
        tab = "[" + ", ".join(lean_world(w) for w in hit) + "]"
        lines.append(f"def t{k} : List (List (Option Bool)) := {tab}")
        lines.append(f'#eval IO.println s!"J{k} {{famIdx (possibleB (hitsOf t{k})) {n}}} | '
                     f'{{famIdx (guaranteedB (hitsOf t{k})) {n}}}"')
    fd, path = tempfile.mkstemp(prefix="zbackward_bridge_", suffix=".lean", dir=LEAN)
    with os.fdopen(fd, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")
    try:
        r = subprocess.run(["lake", "env", "lean", path], cwd=LEAN, capture_output=True, text=True, timeout=1800)
    finally:
        os.unlink(path)
    if r.returncode != 0:
        raise SystemExit("LEAN FAILED:\n" + (r.stdout + r.stderr)[-3000:])
    res = {}
    for l in r.stdout.splitlines():
        if l.startswith("J"):
            head, rest = l.split(" ", 1)
            p, g = rest.split(" | ")
            res[int(head[1:])] = (sorted(sorted(x) for x in eval(p)), sorted(sorted(x) for x in eval(g)))
    return [res[k] for k in range(len(jobs))]


def main():
    ok = fail = 0
    bad = []
    cs = cases()
    jobs = [(len(c[2]), table(*c)) for c in cs]
    got = kernel(jobs)
    for k, (phi, marking, grounds, target, by_disp) in enumerate(cs):
        kp, kg = got[k]
        n = len(grounds)
        for route, use_tree in (("tree", True), ("enum", False)):
            r = ZB.backward(phi, marking, target, by_disposition=by_disp, use_tree=use_tree)
            if "отказ" in r:
                bad.append((k, route, "refused")); fail += 1; continue
            if r["already"]:
                good = kp == [[]] and kg == [[]]
            elif route == "tree" or n <= ZB.MAX_K:
                good = (as_idx(r["possible"], grounds) == kp and as_idx(r["guaranteed"], grounds) == kg
                        and (r["possible_none"] is True) == (kp == []) and (r["guaranteed_none"] is True) == (kg == []))
            else:   # cut enumeration: the sets it lists are the kernel's sets up to MAX_K; never "none" for sure
                small = lambda fam: [s for s in fam if len(s) <= ZB.MAX_K]
                good = (as_idx(r["possible"], grounds) == small(kp) and as_idx(r["guaranteed"], grounds) == small(kg)
                        and r["possible_none"] is not True and r["guaranteed_none"] is not True)
            if good:
                ok += 1
            else:
                fail += 1
                bad.append((k, route, ZB._show(phi) if hasattr(ZB, "_show") else phi, marking, target,
                            r["possible"], r["guaranteed"], kp, kg))
    import ztljudge as ZJ
    nc_ok = nc_fail = 0
    for k, (phi, marking, grounds, target, by_disp) in enumerate(cs):
        if target != ZB.TERMINAL or not by_disp:
            continue
        kp, kg = got[k]
        if kg == [[]]:
            continue                                        # already settled: nothing to check
        nc = ZJ.next_check(ZB._show(phi), marking)
        single_g = [s[0] for s in kg if len(s) == 1]
        single_p = [s[0] for s in kp if len(s) == 1]
        if single_g:
            good = nc is not None and nc["settles"] and grounds.index(nc["atom"]) in single_g
        elif single_p:
            good = nc is not None and not nc["settles"] and grounds.index(nc["atom"]) in single_p
        else:
            good = nc is None or (not nc["settles"] and nc["if_T"] not in ZB.TERMINAL and nc["if_F"] not in ZB.TERMINAL)
        if good:
            nc_ok += 1
        else:
            nc_fail += 1
            bad.append(("next_check", k, ZB._show(phi), marking, nc, kp, kg))
    fail += nc_fail
    print(f"next_check vs the kernel's size-1 sets: {nc_ok} agree, {nc_fail} differ")
    # MUTATION: the first non-already case with a non-empty possible family, one set dropped from Python's answer
    mutation_seen = False
    for k, (phi, marking, grounds, target, by_disp) in enumerate(cs):
        r = ZB.backward(phi, marking, target, by_disposition=by_disp)
        if not r["already"] and r["possible"]:
            mut_k = k
            mutation_seen = as_idx(r["possible"][1:], grounds) != got[k][0]
            break
    print(f"cases {len(cs)} (grounds 1..5, repeated grounds in some), routes tree+enum: {ok} agree, {fail} differ")
    for b in bad[:5]:
        print("  DIFF", b)
    print(f"mutation (case {mut_k}, one set dropped from Python's family): {'caught' if mutation_seen else 'NOT CAUGHT'}")
    if fail == 0 and mutation_seen:
        print("ZBACKWARD LEAN BRIDGE GREEN")
    else:
        print("ZBACKWARD LEAN BRIDGE RED")
        sys.exit(1)


if __name__ == "__main__":
    main()
