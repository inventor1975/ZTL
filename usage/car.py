# -*- coding: utf-8 -*-
"""
Usage 1: buying a used car — everyday life on the core, WITH TIME.

The lemon market (Akerlof 1970) is ZTL's home turf stated as economics:
the seller's words are UNVERIFIED INPUTS, and paying for them is truth
on credit. Here the deal is written in ZFL (the studio's formal
language, genre "statement"), extended with the E24 temporal field —
a "timeline" of verifications: one tick = one check that costs money
(registry lookup, mechanic, notary). The core then answers the question
the buyer actually has:

    WHICH CHECKS CAN I SKIP, AND WHEN CAN I STOP PAYING FOR THEM?

The temporal layer's answer is the warranty grade: once the verdict is
HEREDITARY (on the shelf), the remaining checks buy NOTHING — stop
paying. Three genuine ZFL documents run through the real pipeline
(zfl.validate -> engine.run, no shortcuts):

  S1 PRIVATE SELLER, all checks pass: the deal is
     safe = pledge_free AND papers_ok AND mileage_honest AND no_wreck.
     Zero trust holds the verdict at F ("do not buy yet") on grade U
     through THREE passed checks — default deny to the very last tick,
     then one jump F/U -> T/H. Buying early = buying on credit.
  S2 THE REGISTRY SAYS PLEDGED (first check fails): F/hereditary at
     tick 1 — SETTLED EARLY, the other three checks buy nothing.
     Walk away; the mechanic's fee is saved. Bad news is CHEAP in ZTL:
     one F grounds a conjunction forever (denial is free).
  S3 DEALER WITH A WARRANTY — the selector of E24 §6 in the flesh:
     safe = papers_ok AND (dealer_warranty OR (mileage_honest AND
     no_wreck)). Verifying WHICH WORLD you are in (dealer:=T) plus the
     papers settles the deal T/hereditary with mileage and wreck still
     unverified — the warranty covers them, 2 checks saved. In the
     private-seller world (dealer:=F) both checks remain mandatory.

MEASURED (this file, deterministic): S1 F/U,F/U,F/U -> T/H at tick 4,
0 checks saved; S2 F/H at tick 1, 3 checks saved; S3 T/H at tick 2,
2 checks saved. The asymmetry S1 vs S2 is the zero-trust economy in
one household scene: an affirmation must earn EVERY input, a denial is
grounded by ONE.
"""

import json
import os
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(_ROOT, "tool"))
sys.path.insert(0, _ROOT)

import zfl                                                # noqa: E402
import engine                                             # noqa: E402


def run_doc(title, doc_json):
    doc, parsed, issues = zfl.validate(doc_json)
    hard = [i for i in issues if i["level"] == "error"]
    assert not hard, f"{title}: ZFL rejected: {hard}"
    report = engine.run(doc, parsed)
    print(f"\n### {title}")
    for step in report["chronicle"]:
        note = f"   [{step['note']}]" if "note" in step else ""
        print(f"  t={step['tick']}  {step['event']:22s} verdict "
              f"{step['verdict']}/{step['warranty']:18s} "
              f"marks left {step['marks_left']}{note}")
    saved = report["checks_saved"]
    print(f"  settled at tick {report['settled_at']}; checks saved: {saved}")
    return report


CHECKS = """
  the four checks and their price tags:
    pledge_free     - registry lookup      (is the car collateral?)
    papers_ok       - notary / police desk (are the documents genuine?)
    mileage_honest  - service history pull (is the odometer honest?)
    no_wreck        - independent mechanic (was it totaled?)
"""

S1 = json.dumps({
    "genre": "statement",
    "atoms": {"pledge_free": {"status": "Z"}, "papers_ok": {"status": "Z"},
              "mileage_honest": {"status": "Z"}, "no_wreck": {"status": "Z"}},
    "assert": "and(pledge_free, and(papers_ok, and(mileage_honest, no_wreck)))",
    "timeline": [{"atom": "pledge_free", "value": "T"},
                 {"atom": "papers_ok", "value": "T"},
                 {"atom": "mileage_honest", "value": "T"},
                 {"atom": "no_wreck", "value": "T"}]})

S2 = json.dumps({
    "genre": "statement",
    "atoms": {"pledge_free": {"status": "Z"}, "papers_ok": {"status": "Z"},
              "mileage_honest": {"status": "Z"}, "no_wreck": {"status": "Z"}},
    "assert": "and(pledge_free, and(papers_ok, and(mileage_honest, no_wreck)))",
    "timeline": [{"atom": "pledge_free", "value": "F"}]})

S3 = json.dumps({
    "genre": "statement",
    "atoms": {"dealer_warranty": {"status": "Z"}, "papers_ok": {"status": "Z"},
              "mileage_honest": {"status": "Z"}, "no_wreck": {"status": "Z"}},
    "assert": "and(papers_ok, or(dealer_warranty,"
              " and(mileage_honest, no_wreck)))",
    "timeline": [{"atom": "dealer_warranty", "value": "T"},
                 {"atom": "papers_ok", "value": "T"}]})


if __name__ == "__main__":
    print("=" * 72)
    print("USAGE 1. THE USED CAR: everyday life on the core, with time")
    print("        (ZFL statement + E24 timeline; checks cost money)")
    print("=" * 72)
    print(CHECKS)

    r1 = run_doc("S1: private seller — every check passes", S1)
    g1 = [(s["verdict"], s["warranty"]) for s in r1["chronicle"]]
    assert g1 == [("F", "until-verification")] * 4 + [("T", "hereditary")]
    print("  -> zero trust holds 'do not buy' through three PASSED checks:")
    print("     an affirmation must earn every input; buying early is credit.")

    r2 = run_doc("S2: the registry says PLEDGED — first check fails", S2)
    assert r2["settled_at"] == 1 and r2["checks_saved"] == 3
    assert r2["chronicle"][1]["warranty"] == "hereditary"
    print("  -> bad news is cheap: one F grounds the refusal forever;")
    print("     walk away, the mechanic's fee is saved.")

    r3 = run_doc("S3: dealer with a warranty — the selector", S3)
    assert r3["settled_at"] == 2 and r3["checks_saved"] == 2
    print("  -> verify WHICH WORLD you are in: the dealer's warranty covers")
    print("     mileage and wreck — two checks never need to be paid for.")

    print("\n  == the buyer's law, measured ==")
    print("  affirmation: earned at the LAST tick (S1, 0 saved);")
    print("  denial: grounded at the FIRST failure (S2, 3 saved);")
    print("  routing: verify the selector first (S3, 2 saved).")
    print("  Once HEREDITARY, every remaining check buys nothing — stop paying.")
