#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Phase A evaluator — emits one CLWR per gate (frozen Protocol R-06/R-07).

PROHIBITED for result-bearing use before EXPERIMENT_FREEZE_PACKAGE_ACCEPTED=true.
Usage: evaluate.py <markings_dir> <formulas.json> <judge_pin.json> <claimcontext_id> <out_dir>
"""
import hashlib, json, os, sys, time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", ".."))
from ztljudge import judge  # the pinned kernel

def sha(b): return hashlib.sha256(b).hexdigest()

def main(markdir, formulas_p, pin_p, claimctx, out):
    os.makedirs(out, exist_ok=True)
    spec = json.load(open(formulas_p))
    pin = json.load(open(pin_p))
    fhash = sha(open(formulas_p, "rb").read())
    rows = []
    for g in spec["gates"]:
        mp = os.path.join(markdir, g["gate_id"] + ".marking.json")
        mdoc = json.load(open(mp))
        marking = {a: rec["status"] for a, rec in mdoc["marking"].items()}
        res = judge(g["formula"], {k: v for k, v in marking.items() if v in ("T", "F")})
        clwr = {
            "clwr_of": g["gate_id"],
            "formula": g["formula"],
            "formula_set_sha256": fhash,
            "marking_sha256": sha(open(mp, "rb").read()),
            "judge_identity": pin,
            "verdict": res["verdict"],
            "disposition": res["disposition"],
            "grade": res["grade"],
            "weak_links": sorted(res["unverified"]),
            "atom_provenance": {a: rec.get("witness") for a, rec in mdoc["marking"].items()},
            "input_artifacts": {"marking_file": mp},
            "invocation_time": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "claim_context_id": claimctx,
        }
        p = os.path.join(out, g["gate_id"] + ".clwr.json")
        json.dump(clwr, open(p, "w"), indent=1, ensure_ascii=False)
        rows.append((g["gate_id"], res["disposition"], res["grade"], len(res["unverified"])))
    for r in rows: print("  %-26s %-10s %-18s weak=%d" % r)

if __name__ == "__main__":
    main(*sys.argv[1:6])
