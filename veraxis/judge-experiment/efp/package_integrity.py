#!/usr/bin/env python3
"""Static package-integrity check (no corpus evaluation).
Asserts gate-id set equality across formulas / templates / ground-truth,
count 37, and EH-4 + excluded partition. Usage: package_integrity.py
"""
import json, sys
F = {g["gate_id"] for g in json.load(open("formulas.json"))["gates"]}
T = set(json.load(open("claim-context-templates.json"))["gates"].keys())
G = set(json.load(open("ground-truth.json"))["gates"].keys())
gt = json.load(open("ground-truth.json"))
eh4 = set(gt["EH4_population_gate_ids"]); exc = set(gt["excluded_gate_ids"])
ok = True
def chk(name, cond):
    global ok
    print(f"  {'PASS' if cond else 'FAIL'}  {name}")
    ok = ok and cond
chk("formulas == templates gate-set", F == T)
chk("formulas == ground-truth gate-set", F == G)
chk("gate count == 37", len(F) == 37)
chk("EH4 + excluded == all gates", (eh4 | exc) == F)
chk("EH4 ∩ excluded == empty", not (eh4 & exc))
chk("EH4 count == 34", len(eh4) == 34)
chk("excluded count == 3", len(exc) == 3)

# --- mutation-denominator consistency (static; non-result-bearing) ---
den = json.load(open("mutation-denominators.json"))["classes"]
ORDER = ["missing_witness_or_evidence","corrupted_hashes","schema_drift",
         "counter_inconsistency","contradictory_gate_facts","missing_atoms",
         "false_positive_adapter_markings","altered_identity_environment"]
chk("mutation classes == 8", len(den) == 8 and set(den) == set(ORDER))
chk("frozen_N <= structural_ceiling (every class)",
    all(den[c]["frozen_N"] <= den[c]["structural_ceiling"] for c in ORDER))
vec = [den[c]["frozen_N"] for c in ORDER]
chk("frozen_N vector == [10,10,10,7,3,10,10,10]", vec == [10,10,10,7,3,10,10,10])
sc = json.load(open("scoring-constants.json"))
chk("scoring gates_total == 37", sc["gates_total"] == 37)
chk("scoring atoms_total == 91", sc["atoms_total"] == 91)

print("package integrity:", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
