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
print("package integrity:", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
