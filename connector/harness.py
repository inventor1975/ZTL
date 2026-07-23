"""Conformance harness for the ZTL Connector (SPEC §4).

Run:  python3 connector/harness.py

What it proves:
  1. The reference `judge_warrant` reproduces every fixture's expected verdict
     record (verdict / grade / disposition / unverified).
  2. The rule pin is consistent: the fixtures' `rule.hash` equals the top-level
     `rule_hash`, and both are what the fixtures declare.
  3. Sign -> verify round-trips, and verification is offline (reference + artifact
     + warrant-form only — no protocol server): the anti-monopoly property.
  4. A tampered artifact fails verification (negative control).

A CONSUMER re-implementation conforms iff it reproduces the same expected
records on the same byte-identical fixtures (step 1) — that is the cross-language
agreement check. This harness IS the reference side of that check.
"""
from __future__ import annotations

import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))

from connector.signer import Signer, available_schemes  # noqa: E402
from connector.verdict import judge_warrant, verify_artifact  # noqa: E402

FIXTURES = os.path.join(HERE, "fixtures", "ZTL-CORE-JUDGE-fixtures-v0.1.json")
WF_SCHEMA = os.path.join(HERE, "schema", "warrant-form.schema.json")
VA_SCHEMA = os.path.join(HERE, "schema", "verdict-artifact.schema.json")

_FIELDS = ("verdict", "grade", "disposition", "unverified")


def _validate_schemas(data: dict, fixtures: list) -> str:
    """Formally validate every warrant-form and produced artifact against the
    JSON schemas. Degrades gracefully if jsonschema is not installed."""
    try:
        import jsonschema
    except ImportError:
        return "schema validation SKIPPED (jsonschema not installed)"
    wf_schema = json.load(open(WF_SCHEMA, encoding="utf-8"))
    va_schema = json.load(open(VA_SCHEMA, encoding="utf-8"))
    signer = Signer("ed25519")
    n = 0
    for fx in fixtures:
        wf = _full_warrant(data, fx)
        jsonschema.validate(wf, wf_schema)
        jsonschema.validate(judge_warrant(wf, signer), va_schema)
        n += 1
    return f"schema-valid: {n} warrant-forms + {n} artifacts"


def _full_warrant(data: dict, fx: dict) -> dict:
    """Fixtures carry the rule once at top level; splice it into each warrant."""
    return {**fx["warrant"], "rule": data["rule"]}


def run() -> int:
    with open(FIXTURES, encoding="utf-8") as f:
        data = json.load(f)

    fixtures = data["fixtures"]
    fails = []

    # ---- 2. rule pin consistency --------------------------------------------
    assert data["rule"]["hash"] == data["rule_hash"], \
        "rule.hash != top-level rule_hash (pin mismatch)"

    # ---- 1. reference reproduces every expected record ----------------------
    for fx in fixtures:
        wf = _full_warrant(data, fx)
        art = judge_warrant(wf)
        got = {k: art[k] for k in _FIELDS}
        exp = {k: fx["expected"][k] for k in _FIELDS}
        ok = got == exp
        print(f"  [{'OK ' if ok else 'XX '}] {fx['name']:<28} "
              f"{got['verdict']}/{got['grade']} -> {got['disposition']}")
        if not ok:
            fails.append((fx["name"], exp, got))

    # ---- 3. sign -> verify round-trip, offline ------------------------------
    signer = Signer("ed25519")
    wf0 = _full_warrant(data, fixtures[0])
    signed = judge_warrant(wf0, signer)
    rep = verify_artifact(signed, wf0)
    assert rep["ok"] and rep["checks"]["signature_valid"], \
        f"signed artifact failed verification: {rep}"
    print(f"  [OK ] sign->verify round-trip     scheme={signed['signature']['scheme']}")

    # ---- 4. negative control: tamper is caught ------------------------------
    tampered = dict(signed)
    tampered["verdict"] = "F" if signed["verdict"] != "F" else "T"
    rep_bad = verify_artifact(tampered, wf0)
    assert not rep_bad["ok"], "tampered artifact wrongly verified as ok"
    print(f"  [OK ] tamper rejected             "
          f"(verdict_matches={rep_bad['checks']['verdict_matches']})")

    # ---- 5. formal schema validation ----------------------------------------
    print(f"  [OK ] {_validate_schemas(data, fixtures)}")

    # ---- report -------------------------------------------------------------
    print()
    print(f"  schemes available: {available_schemes()}")
    if fails:
        print(f"\nFAIL: {len(fails)} fixture(s) diverged from the reference:")
        for name, exp, got in fails:
            print(f"    {name}: expected {exp} got {got}")
        return 1
    print(f"\nPASS: {len(fixtures)}/{len(fixtures)} fixtures + sign/verify + tamper control.")
    return 0


if __name__ == "__main__":
    raise SystemExit(run())
