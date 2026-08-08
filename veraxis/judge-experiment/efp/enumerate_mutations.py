#!/usr/bin/env python3
"""Enumerate structurally valid mutation opportunities per class over the frozen
corpus, and freeze per-class denominators (Protocol §23: N>=10 per class or the
enumerated structural ceiling). Opportunities are counted from the same
persisted artifacts the formulas bind. Usage: enumerate_mutations.py <ledger> <zip> <formulas.json> <out>
"""
import json, subprocess, sys, zipfile

LEDGER, ZIPPATH, FORMULAS, OUT = sys.argv[1:5]
spec = json.load(open(FORMULAS))
gates = spec["gates"]
atoms = [a for g in gates for a in g["atoms"]]

def count(rule_names):
    return sum(1 for a in atoms if a["rule"] in rule_names)

# structurally valid opportunity = an artifact site a controller can mutate so
# that exactly one atom class is targeted
classes = {
 "missing_witness_or_evidence": count({"member_identity", "zip_member_identity", "file_absent",
                                       "file_bytes", "file_equals"}),          # delete/blank a bound artifact
 "corrupted_hashes":            count({"member_identity", "zip_member_identity",
                                       "manifest_accounting", "zip_manifest_accounting", "json_field"}),
 "schema_drift":                count({"manifest_accounting", "zip_manifest_accounting", "json_field",
                                       "json_all_true"}),                       # rename a bound field
 "counter_inconsistency":       sum(1 for a in atoms if a["rule"] == "json_field"
                                    and isinstance(a["args"].get("expected"), int)),
 "contradictory_gate_facts":    count({"junit_counts", "junit_failing_set", "argv_equals"}),
 "missing_atoms":               len(atoms),                                     # drop any harvested atom's source
 "false_positive_adapter_markings": len(atoms),                                 # plant unwitnessed T
 "altered_identity_environment": count({"tree_identity", "path_confinement", "changed_file_set",
                                        "argv_equals", "ast_confinement"}),
}
den = {}
for cls, ceiling in classes.items():
    den[cls] = {"structural_ceiling": ceiling, "frozen_N": min(10, ceiling) if ceiling < 10 else 10}
    if ceiling < 10:
        den[cls]["note"] = "fewer than ten structurally valid opportunities; all enumerated opportunities to be used (Protocol §23)"
out = {"denominators_id": "M1-EXPERIMENT-MUTATION-DENOMINATORS-v0.1",
       "rule": "N >= 10 planted per class, or the enumerated structural ceiling (all used, ceiling recorded before execution)",
       "classes": den,
       "atoms_total": len(atoms), "gates_total": len(gates)}
json.dump(out, open(OUT, "w"), indent=1, ensure_ascii=False)
for c, v in den.items():
    print(f"  {c:34s} ceiling={v['structural_ceiling']:3d} frozen_N={v['frozen_N']}")
