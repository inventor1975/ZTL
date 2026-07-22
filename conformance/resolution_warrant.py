# -*- coding: utf-8 -*-
"""
resolution_warrant — the REFERENCE evaluator of MR-WARRANT-RESOLUTION-001.

This is the single source of the warrant SEMANTICS for the MindReef resolution
gate. Consumers (e.g. MindReef's native PHP) re-implement the rule locally and
prove they replicate this reference by passing the SAME shared fixtures
(conformance/MR-WARRANT-RESOLUTION-001.json) — the reference is never a runtime
dependency of the consumer, only the definition of correctness.

The rule (MR-WARRANT-RESOLUTION-001, v1.0.0): a topic may transition to
'resolved' only if every idea has a KNOWN, DECIDED status (approved/rejected);
any pending — or unknown/missing/null/malformed — status blocks it (fail
closed) and it is downgraded to 'discussing'. A non-'resolved' proposal passes
through unchanged.

Claim ceiling: proves only the absence of a PRESENTED pending/unrecognised
status — not synthesis quality, unrecorded dissent, correctness of the statuses
themselves, authority to close, or sufficiency for external reliance.

Run:  python3 conformance/resolution_warrant.py   (checks all fixtures)
"""
import hashlib
import json
import os

RULE_ID = "MR-WARRANT-RESOLUTION-001"
VERSION = "1.0.0"
DECIDED = ("approved", "rejected")          # the only statuses that do NOT block
_HERE = os.path.dirname(os.path.abspath(__file__))
_SPEC = os.path.join(_HERE, "MR-WARRANT-RESOLUTION-001.json")


def gate(proposed, idea_statuses):
    """MR-WARRANT-RESOLUTION-001 reference. Returns the admissible
    resolution_status. Fail closed: any status not in DECIDED blocks a
    'resolved' proposal (pending, unknown, None, '', anything)."""
    if proposed != "resolved":
        return proposed
    if all(s in DECIDED for s in idea_statuses):
        return "resolved"
    return "discussing"


def rule_hash():
    """A stable hash of the normative definition — a semantic version anchor
    both implementations can pin, so a silent divergence is detectable."""
    canon = json.dumps({"rule_id": RULE_ID, "version": VERSION,
                        "decided": list(DECIDED),
                        "resolved_requires": "all idea statuses in decided",
                        "fail_closed": True, "passthrough_non_resolved": True},
                       sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canon.encode()).hexdigest()


def main():
    spec = json.load(open(_SPEC, encoding="utf-8"))
    assert spec["rule_id"] == RULE_ID and spec["version"] == VERSION, \
        "spec/reference rule id or version mismatch"
    assert spec["rule_hash"] == rule_hash(), \
        "spec/reference semantic hash mismatch"
    print(f"{RULE_ID} v{VERSION}  rule_hash={rule_hash()[:16]}…")
    print(f"checking {len(spec['fixtures'])} shared fixtures "
          "(the same set the PHP consumer must pass)\n")
    fails = []
    for fx in spec["fixtures"]:
        got = gate(fx["proposed"], fx["idea_statuses"])
        ok = got == fx["expected"]
        if not ok:
            fails.append(fx["id"])
        print(f"  [{'OK ' if ok else 'FAIL'}] {fx['id']:28s} "
              f"{fx['kind']:11s} → {got}  (expect {fx['expected']})")
    print()
    assert not fails, f"reference failed fixtures: {fails}"
    print(f"RESOLUTION-WARRANT REFERENCE GREEN — {len(spec['fixtures'])} "
          "fixtures pass; this is the semantics the PHP consumer replicates.")


if __name__ == "__main__":
    main()
