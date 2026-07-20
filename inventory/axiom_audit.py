# -*- coding: utf-8 -*-
"""
axiom_audit — the per-THEOREM axiom ledger of the Lean corpus.

Why this exists. The preprint (§8) claims that `#print axioms` over the
WHOLE corpus returns "does not depend on any axioms". Until now that was
backed by 103 hand-placed `#print axioms` lines against 321 theorems in
the sources. The defence is sound in principle — a dirty lemma infects
every theorem that uses it, so a clean print at the top transitively
covers its dependencies — but it is an ARGUMENT, and an unused orphan
theorem would escape it entirely. The claim ceiling of an argument is
lower than that of a measurement.

So this stand measures it instead: it extracts every theorem and lemma
name from every module, generates one `#print axioms` per name, runs the
whole thing through Lean, and fails loudly if a single line says anything
other than "does not depend on any axioms".

It also fails on an ORPHAN module: one that carries theorems but is
neither a build target nor imported by one, so no automation ever sees
it. That is not hypothetical — `QuantumWitness.lean` (the MO2 quantum
pole, load-bearing for PSSL) sat outside `defaultTargets` from its
writing until 2026-07-20 and was checked by nobody.

MEASURED (2026-07-20, Lean 4.29.1, clean build, 16 modules):
  theorems audited ............................... 321   all empty-list

Run:  python3 inventory/axiom_audit.py
Exit 0 = every theorem in the corpus is on the empty axiom list.
"""
import json
import os
import re
import subprocess
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
_LEAN = os.path.join(os.path.dirname(_HERE), "lean")

# Built by lakefile.toml `defaultTargets`, in dependency order. Read from
# the lakefile rather than duplicated, so this stand cannot drift from the
# build: a module added to the corpus and forgotten here would otherwise
# go unaudited — which is exactly how QuantumWitness stayed invisible
# until 2026-07-20.
def build_targets():
    src = open(os.path.join(_LEAN, "lakefile.toml"), encoding="utf-8").read()
    m = re.search(r"defaultTargets\s*=\s*\[(.*?)\]", src, re.S)
    if not m:
        raise SystemExit("lakefile.toml: no defaultTargets")
    return re.findall(r'"([^"]+)"', m.group(1))


def orphans(targets):
    """Modules present in lean/ but built by nobody — the F2 class of bug."""
    on_disk = {f[:-5] for f in os.listdir(_LEAN) if f.endswith(".lean")}
    reachable = set(targets)
    for m in list(on_disk):
        src = open(os.path.join(_LEAN, m + ".lean"), encoding="utf-8").read()
        for imp in re.findall(r"^import\s+(\S+)", src, re.M):
            if m in reachable:
                reachable.add(imp)
    return sorted(on_disk - reachable)

CLEAN = "does not depend on any axioms"

_DECL = re.compile(r"^(?:private\s+|protected\s+)?(?:theorem|lemma)\s+"
                   r"([A-Za-z_][\w'.!?]*)")
_NS = re.compile(r"^namespace\s+([A-Za-z_][\w.]*)")
_END = re.compile(r"^end\s+([A-Za-z_][\w.]*)")


def theorem_names(module):
    """Fully qualified theorem names of a module, in source order."""
    src = open(os.path.join(_LEAN, module + ".lean"), encoding="utf-8").read()
    stack, names = [], []
    for line in src.split("\n"):
        s = line.strip()
        m = _NS.match(s)
        if m:
            stack.append(m.group(1))
            continue
        m = _END.match(s)
        if m and stack and m.group(1) == stack[-1]:
            stack.pop()
            continue
        m = _DECL.match(s)
        if m:
            names.append(".".join(stack + [m.group(1)]))
    return names


def audit(modules, imports):
    """Generate one #print axioms per theorem, run Lean, return the lines."""
    names = {m: theorem_names(m) for m in modules}
    body = [f"import {m}" for m in imports] + [""]
    for m in modules:
        body += [f"-- {m} ({len(names[m])})"] + \
                [f"#print axioms {n}" for n in names[m]]
    path = os.path.join(_LEAN, "_axiom_audit_scratch.lean")
    open(path, "w", encoding="utf-8").write("\n".join(body) + "\n")
    try:
        env = dict(os.environ, LEAN_PATH=os.path.join(_LEAN,
                                                      ".lake/build/lib/lean"))
        r = subprocess.run(["lean", "_axiom_audit_scratch.lean"], cwd=_LEAN,
                           capture_output=True, text=True, timeout=1800,
                           env=env)
    finally:
        os.remove(path)
    out = [ln for ln in (r.stdout + r.stderr).split("\n") if ln.strip()]
    return names, out


def report(label, names, out):
    total = sum(len(v) for v in names.values())
    dirty = [ln for ln in out if CLEAN not in ln]
    print(f"\n  {label}: {total} theorems in {len(names)} modules")
    for m, v in names.items():
        print(f"    {m:18s} {len(v):3d}")
    print(f"    axiom-print lines returned : {len(out)}")
    print(f"    on the EMPTY axiom list    : {len(out) - len(dirty)}")
    if dirty:
        print(f"    NOT CLEAN ({len(dirty)}):")
        for ln in dirty:
            print(f"      {ln}")
    return dirty, total, len(out)


if __name__ == "__main__":
    print("=" * 72)
    print("AXIOM AUDIT — every theorem of the corpus, not a sample")
    print("=" * 72)

    if not os.path.isdir(os.path.join(_LEAN, ".lake/build/lib/lean")):
        print("\n  no build artifacts; run `lake build` in lean/ first")
        sys.exit(1)

    targets = build_targets()
    # An orphan carrying theorems is the F2 bug: content checked by no
    # automation. An orphan with none is a generator script (BridgeGen
    # feeds bridge.py by #eval) — nothing to audit, so it is only noted.
    stray = [(m, len(theorem_names(m))) for m in orphans(targets)]
    unchecked = [m for m, n in stray if n]
    for m, n in stray:
        if not n:
            print(f"\n  note: {m}.lean is built by nobody, but carries no "
                  "theorems (generator script) — nothing to audit")
    if unchecked:
        print(f"\n  RED: {len(unchecked)} module(s) with theorems built by "
              "nobody — not a target, not imported by one:")
        for m in unchecked:
            print(f"    {m}.lean  ({dict(stray)[m]} theorems)")
        print("  Their theorems are checked by no automation. Add them to "
              "defaultTargets in lean/lakefile.toml.")
        sys.exit(1)

    n1, o1 = audit(targets, targets)
    d1, t1, c1 = report("build targets", n1, o1)

    print("\n" + "=" * 72)
    bad, missed = d1, t1 - c1
    t2 = 0
    if bad:
        print(f"RED: {len(bad)} theorem(s) carry axioms")
        sys.exit(1)
    if missed:
        print(f"RED: {missed} theorem(s) produced no axiom line "
              "(name extraction out of step with the sources)")
        sys.exit(1)
    print(f"ALL CLEAN: {t1} theorems across {len(targets)} modules, "
          "every one on the empty axiom list.")
