#!/usr/bin/env python3
"""Provenance audit (Protocol §19.5, §24.5): scan markings for provenance-less T/F.

A T/F without a witness object, or with a witness lacking a content identity
(blob sha / zip sha / commit sha), is a harvesting-layer failure. Scored
separately from judge correctness. Usage: provenance_audit.py <markings_dir>
"""
import json, os, sys

def witness_ok(w):
    if not isinstance(w, dict): return False
    idish = ("sha256", "tree", "head", "zip_sha256", "paths_sha256")
    return any(k in w for k in idish)

def main(d):
    bad = []
    n = 0
    for f in sorted(os.listdir(d)):
        if not f.endswith(".marking.json"): continue
        doc = json.load(open(os.path.join(d, f)))
        for atom, rec in doc["marking"].items():
            n += 1
            if rec["status"] in ("T", "F") and not witness_ok(rec.get("witness")):
                bad.append((doc["gate_id"], atom, rec["status"]))
    print(f"atoms scanned: {n}; provenance-less T/F: {len(bad)}")
    for b in bad: print("  VIOLATION:", *b)
    return 1 if bad else 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
