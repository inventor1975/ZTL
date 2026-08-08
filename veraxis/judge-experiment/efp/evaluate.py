#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Phase A evaluator — emits one R-06/R-07/R-15-conformant CLWR per gate.

PROHIBITED for result-bearing use before EXPERIMENT_FREEZE_PACKAGE_ACCEPTED=true.

Usage: evaluate.py <markings_dir> <formulas.json> <judge-pin.json> <claim-context-templates.json> <out_dir>

Canonicalization (frozen): canon(obj) = json.dumps(obj, sort_keys=True,
separators=(",", ":")) encoded UTF-8. formula_sha256 = SHA-256 of the exact
formula string (UTF-8). marking_sha256 = SHA-256 of canon(marking-status-map).
JudgeContext identity = SHA-256 of canon({formula_sha256, marking_sha256,
judge_pin_sha256}). ClaimContext identity = SHA-256 of canon({template,
judge_context_id}).
"""
import hashlib, json, os, sys, time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", ".."))
from ztljudge import judge  # the pinned kernel

def canon(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()

def sha(b): return hashlib.sha256(b).hexdigest()

R07_FIELDS = ["formula", "formula_sha256", "marking", "marking_sha256",
              "judge_identity", "verdict_and_disposition", "grade", "weak_links",
              "atom_provenance", "input_artifacts", "invocation_time",
              "judge_context_id", "claim_context_id"]

def build_clwr(gate, mdoc, mpath, pin, templates):
    # Full Marking (Protocol §2): atom -> status AND witness references for every non-Z.
    full_marking = {a: {"status": rec["status"], "witness": rec.get("witness")}
                    for a, rec in mdoc["marking"].items()}
    marking_status = {a: rec["status"] for a, rec in mdoc["marking"].items()}
    formula = gate["formula"]
    formula_sha = sha(formula.encode())
    marking_sha = sha(canon(full_marking))          # Marking identity binds witnesses
    status_map_sha = sha(canon(marking_status))     # diagnostic only
    pin_sha = sha(canon(pin))
    judge_ctx = sha(canon({"formula_sha256": formula_sha,
                           "marking_sha256": marking_sha,
                           "judge_pin_sha256": pin_sha}))
    tpl = templates["gates"][gate["gate_id"]]
    claim_ctx = sha(canon({"template": tpl, "judge_context_id": judge_ctx}))
    res = judge(formula, {k: v for k, v in marking_status.items() if v in ("T", "F")})
    mfile = open(mpath, "rb").read()
    return {
        "clwr_of": gate["gate_id"],
        # R-07 field 1: formula and its individual identity
        "formula": formula,
        "formula_sha256": formula_sha,
        # R-07 field 2: the marking itself (with witnesses) and its identity hash
        "marking": full_marking,
        "marking_sha256": marking_sha,
        "status_map_sha256": status_map_sha,
        # field 3: judge identity
        "judge_identity": {**pin, "judge_pin_sha256": pin_sha},
        # field 4-5: verdict/disposition, grade
        "verdict_and_disposition": {"verdict": res["verdict"], "disposition": res["disposition"]},
        "grade": res["grade"],
        # field 6: weak links
        "weak_links": sorted(res["unverified"]),
        # field 7: atom provenance as admitted
        "atom_provenance": {a: rec.get("witness") for a, rec in mdoc["marking"].items()},
        # field 8: input artifacts, hash-bound (R-15)
        "input_artifacts": {"marking_document": {"path": os.path.basename(mpath),
                                                 "bytes": len(mfile), "sha256": sha(mfile)},
                            "formula_set": {"path": "formulas.json"},
                            "source_anchors": gate["source_anchors"]},
        # field 9: invocation time/context
        "invocation_time": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        # field 10: contexts — JudgeContext id + ClaimContext id (R-06)
        "judge_context_id": judge_ctx,
        "claim_context_id": claim_ctx,
        "claim_context_template": tpl,
    }

def main(markdir, formulas_p, pin_p, tpl_p, out):
    os.makedirs(out, exist_ok=True)
    spec = json.load(open(formulas_p))
    pin = json.load(open(pin_p))
    templates = json.load(open(tpl_p))
    fset = open(formulas_p, "rb").read()
    for g in spec["gates"]:
        mp = os.path.join(markdir, g["gate_id"] + ".marking.json")
        mdoc = json.load(open(mp))
        clwr = build_clwr(g, mdoc, mp, pin, templates)
        clwr["input_artifacts"]["formula_set"]["sha256"] = sha(fset)
        clwr["input_artifacts"]["formula_set"]["bytes"] = len(fset)
        missing = [f for f in R07_FIELDS if f not in clwr]
        assert not missing, f"CLWR missing R-07 fields: {missing}"
        p = os.path.join(out, g["gate_id"] + ".clwr.json")
        json.dump(clwr, open(p, "w"), indent=1, ensure_ascii=False)
        print("  %-26s %-10s %-18s weak=%d" % (g["gate_id"],
              clwr["verdict_and_disposition"]["disposition"], clwr["grade"],
              len(clwr["weak_links"])))

if __name__ == "__main__":
    main(*sys.argv[1:6])
