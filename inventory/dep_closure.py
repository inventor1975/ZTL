# -*- coding: utf-8 -*-
"""
dep_closure — native Lean transitive dependency closure for the Veraxis
conformance subset (the gate the package left DEFERRED).

For each of the 28 selected declarations it asks the Lean kernel, not a regex,
which OTHER corpus objects that declaration transitively rests on. It does so
by walking `ConstantInfo` (type + value) via `Expr.getUsedConstants`, keeping
only constants whose defining module is one of our 21 corpus modules, and
recursing only through those. Mathlib / core dependencies are out of scope by
construction — the closure is over the ZTL corpus itself.

Compiler-generated eliminators and internal auxiliaries (`.rec`, `.casesOn`,
`.noConfusion*`, `.brecOn`, `.below`, `.sizeOf`, `.match_*`, `.eq_*`,
`._proof_*`, macro-scoped names) are elided as MECHANICAL: they are implied by
the inductive/def that is already listed. Data constructors (e.g. `V.Z`) are
KEPT — they are meaningful named objects. This choice is stated in the
artifact header so nothing is hidden.

Run:  python3 inventory/dep_closure.py
      → writes VERAXIS-ZTL-deps-v0.1.json
Requires a built corpus (lean/.lake/build) — same precondition as axiom_audit.
"""
import json
import os
import re
import subprocess
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
_LEAN = os.path.join(_ROOT, "lean")
sys.path.insert(0, _HERE)
import axiom_audit as aa                                          # noqa: E402
import conformance_package as cp                                 # noqa: E402

# Path segments that mark a name as a MECHANICAL consequence of a listed
# inductive/definition — Lean generates these for every type, so they add no
# information the parent object does not already imply. Segment-based, so an
# internal like `V.Fm.brecOn.go` is caught by its `brecOn` segment. Authored
# equation lemmas (`imp_def`, `xor_def`) and real instances are NOT here and
# stay in the closure; data constructors stay too.
_MECH_SEG = {"rec", "recAux", "casesOn", "below", "ibelow", "brecOn",
             "binductionOn", "noConfusion", "noConfusionType", "ctorIdx",
             "ofNat", "ofNat_ctorIdx", "toCtorIdx", "sizeOf", "rawCast"}
_MECH_PAT = re.compile(
    r"^(_sizeOf_\d+|match_\d+|eq_\d+|eq_def|_eq_\d+|proof_\d+|_proof_\d+|"
    r"_cstage\d+|_elambda_\d+)$")


def _is_mechanical(name):
    if "._@." in name:                       # macro-scoped hygiene name
        return True
    segs = name.split(".")
    return any(s in _MECH_SEG or _MECH_PAT.match(s) for s in segs)


def _scratch(targets, modules):
    body = [f"import {m}" for m in modules]
    body += ["import Lean", "open Lean Elab Command", "",
             "private def ourModules : List Name := [" +
             ", ".join("`" + m for m in modules) + "]", "",
             "private def isOurs (env : Environment) (n : Name) : Bool :=",
             "  match env.getModuleIdxFor? n with",
             "  | some idx => ourModules.contains (env.header.moduleNames[idx]!)",
             "  | none => false", "",
             "private partial def closure (env : Environment)",
             "    : List Name → NameSet → NameSet",
             "  | [], acc => acc",
             "  | n :: rest, acc =>",
             "    match env.find? n with",
             "    | none => closure env rest acc",
             "    | some ci =>",
             "      let used := ci.type.getUsedConstants ++",
             "        (ci.value?.map (·.getUsedConstants)).getD #[]",
             "      let fresh := used.filter (fun d =>",
             "        isOurs env d && !acc.contains d)",
             "      let acc := fresh.foldl (init := acc) (fun a d => a.insert d)",
             "      closure env (fresh.toList ++ rest) acc", "",
             "run_cmd do",
             "  let env ← getEnv",
             "  let targets : List Name := [" +
             ", ".join("`" + t for t in targets) + "]",
             "  for t in targets do",
             "    let cl := closure env [t] {}",
             "    for d in cl.toList do",
             "      logInfo m!\"DEP {t} {d}\"",
             "    logInfo m!\"END {t}\""]
    return "\n".join(body) + "\n"


def run(targets, modules):
    path = os.path.join(_LEAN, "_dep_closure_scratch.lean")
    open(path, "w", encoding="utf-8").write(_scratch(targets, modules))
    try:
        env = dict(os.environ,
                   LEAN_PATH=os.path.join(_LEAN, ".lake/build/lib/lean"))
        r = subprocess.run(["lean", "_dep_closure_scratch.lean"], cwd=_LEAN,
                           capture_output=True, text=True, timeout=1800, env=env)
    finally:
        os.remove(path)
    lines = (r.stdout + r.stderr).split("\n")
    deps, seen_end, cur = {}, set(), None
    for ln in lines:
        s = ln.strip()
        if s.startswith("DEP "):
            _, t, d = s.split(None, 2)
            deps.setdefault(t, set()).add(d)
        elif s.startswith("END "):
            seen_end.add(s.split(None, 1)[1])
    return deps, seen_end, r.returncode, [l for l in lines if l.strip()]


def main():
    modules = aa.build_targets()
    targets = [n for _, names in cp.SUBSET for n in names]
    if not os.path.isdir(os.path.join(_LEAN, ".lake/build/lib/lean")):
        raise SystemExit("no build artifacts; run `lake build` in lean/ first")

    deps, ended, rc, raw = run(targets, modules)
    processed = [t for t in targets if t in ended]
    unprocessed = [t for t in targets if t not in ended]
    if unprocessed:
        print("Lean output (tail):")
        for l in raw[-25:]:
            print("   ", l)
        raise SystemExit(f"RED: {len(unprocessed)} targets not processed by "
                         f"Lean: {unprocessed}")

    closures = {}
    for t in targets:
        raw_deps = sorted(deps.get(t, set()))
        kept = [d for d in raw_deps if not _is_mechanical(d)]
        closures[t] = {"count": len(kept),
                       "mechanical_elided": len(raw_deps) - len(kept),
                       "closure": kept}

    doc = {
        "artifact": "VERAXIS-ZTL-deps-v0.1",
        "note": ("Native transitive dependency closure of each selected "
                 "declaration over the ZTL corpus (21 modules), computed from "
                 "the Lean kernel via Expr.getUsedConstants over ConstantInfo "
                 "type+value, recursing only through corpus constants. Mathlib "
                 "and Lean-core dependencies are out of scope by construction. "
                 "Compiler-generated eliminators/auxiliaries are elided as "
                 "mechanical (count retained per entry); data constructors are "
                 "kept."),
        "corpus_modules": modules,
        "closures": closures,
    }
    path = os.path.join(_ROOT, "VERAXIS-ZTL-deps-v0.1.json")
    with open(path, "w", encoding="utf-8") as fh:
        json.dump(doc, fh, ensure_ascii=False, indent=2)
        fh.write("\n")
    tot = sum(c["count"] for c in closures.values())
    print(f"wrote {path}: {len(processed)} declarations, "
          f"{tot} corpus dependencies total "
          f"(mechanical elided: {sum(c['mechanical_elided'] for c in closures.values())})")


if __name__ == "__main__":
    main()
