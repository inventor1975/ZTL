# -*- coding: utf-8 -*-
"""
ZTLStudio foundation tests: ZFL parser/validator/back-reading + the
engine on the example zoo — the AI-free part of the pipeline, measured.
"""

import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import zfl
import engine

OK = FAIL = 0


def check(name, cond, detail=""):
    global OK, FAIL
    if cond:
        OK += 1
        print(f"  ✓ {name}")
    else:
        FAIL += 1
        print(f"  ✗ {name} {detail}")


def codes(issues):
    return {i["code"] for i in issues}


if __name__ == "__main__":
    print("=" * 72)
    print("ZTLSTUDIO FOUNDATION: ZFL VALIDATOR + ENGINE (AI-free, measured)")
    print("=" * 72)

    print("\n### Validator: good documents pass")
    liar = json.dumps({"genre": "system",
                       "sentences": {"L": "not(Tr(L))"}})
    doc, parsed, issues = zfl.validate(liar)
    check("liar validates", parsed is not None, str(issues))

    sensor = json.dumps({"genre": "statement",
                         "atoms": {"a": {"status": "Z"},
                                   "b": {"status": "Z"}},
                         "assert": "imp(a, b)"})
    doc2, parsed2, _ = zfl.validate(sensor)
    check("sensor statement validates", parsed2 is not None)

    print("\n### Validator: machine-readable errors for the repair loop")
    bad = [
        ("broken json", "{genre", {"E_JSON"}),
        ("bad genre", '{"genre": "poem"}', {"E_GENRE"}),
        ("undefined atom",
         '{"genre":"statement","assert":"and(x, y)"}',
         {"E_UNDEF_ATOM"}),
        ("Tr in statement",
         '{"genre":"statement","atoms":{"x":{"status":"Z"}},'
         '"assert":"and(x, Tr(x))"}',
         {"E_TR_IN_STATEMENT"}),
        ("bare atom in system",
         '{"genre":"system","sentences":{"L":"not(L)"}}',
         {"E_BARE_ATOM"}),
        ("undefined sentence",
         '{"genre":"system","sentences":{"L":"not(Tr(M))"}}',
         {"E_UNDEF_SENTENCE"}),
        ("Z as constant",
         '{"genre":"statement","atoms":{},"assert":"not(Z)"}',
         {"E_FORMULA"}),
        ("formula syntax",
         '{"genre":"statement","atoms":{},"assert":"and(T"}',
         {"E_FORMULA"}),
        ("formula is a number",
         '{"genre":"system","sentences":{"L": 123}}',
         {"E_TYPE"}),
        ("assert is a list",
         '{"genre":"statement","atoms":{},"assert":["not"]}',
         {"E_TYPE"}),
        ("ask is a string",
         '{"genre":"system","sentences":{"L":"not(Tr(L))"},"ask": 5}',
         {"E_TYPE"}),
    ]
    for name, text, want in bad:
        _, p, iss = zfl.validate(text)
        check(f"{name} → {'/'.join(sorted(want))}",
              p is None and want <= codes(iss), str(codes(iss)))

    dg = json.dumps({"genre": "system",
                     "sentences": {"R": "xnor(Tr(R),Tr(R))"}})
    _, pdg, idg = zfl.validate(dg)
    check("degenerate xnor(A,A) → warning, still valid",
          pdg is not None and "W_DEGENERATE" in codes(idg), str(codes(idg)))

    print("\n### Back-reading: the non-hallucinating auditor")
    br = zfl.back_reading(doc, parsed)
    check("liar reads back", "not (\u201cL\u201d is true)" in br, br)
    br2 = zfl.back_reading(doc2, parsed2)
    check("sensor reads back",
          "if \u201ca\u201d then \u201cb\u201d" in br2
          and "UNVERIFIED" in br2, br2)

    print("\n### Engine: the zoo through ZFL end to end")
    rep = engine.run(doc, parsed)
    kinds = {p["kind"] for p in rep["passports"]}
    check("liar → PARADOX", kinds == {"PARADOX"}, str(kinds))
    check("liar quarantined", rep["quarantined"] == ["L"])

    rep2 = engine.run(doc2, parsed2)
    check("sensor → verdict F (Z→Z is not forced)", rep2["verdict"] == "F")
    check("sensor → warranty until-verification",
          rep2["warranty"] == "until-verification")
    check("sensor completions listed", len(rep2["completions"]) == 4)

    croc = json.dumps({"genre": "system",
                       "sentences": {"R": "Tr(M)", "M": "not(Tr(R))"}})
    d3, p3, _ = zfl.validate(croc)
    rep3 = engine.run(d3, p3)
    check("crocodile → PARADOX, period 4",
          rep3["passports"][0]["kind"] == "PARADOX"
          and "period 4" in rep3["passports"][0]["detail"],
          str(rep3["passports"]))

    tt = json.dumps({"genre": "system", "sentences": {"tau": "Tr(tau)"}})
    d4, p4, _ = zfl.validate(tt)
    rep4 = engine.run(d4, p4)
    check("truth-teller → UNDERDETERMINED with 2 stipulations",
          rep4["passports"][0]["kind"] == "UNDERDETERMINED"
          and len(rep4["stipulations"][0]["models"]) == 2)

    russell = json.dumps({"genre": "system", "sentences": {
        "a_in_a": "F", "a_in_b": "F", "a_in_R": "not(Tr(a_in_a))",
        "b_in_a": "F", "b_in_b": "T", "b_in_R": "not(Tr(b_in_b))",
        "R_in_a": "F", "R_in_b": "F", "R_in_R": "not(Tr(R_in_R))"}})
    d5, p5, _ = zfl.validate(russell)
    rep5 = engine.run(d5, p5)
    check("Russell → 8 grounded, R_in_R quarantined",
          len(rep5["grounded"]) == 8
          and rep5["quarantined"] == ["R_in_R"], rep5["summary"])

    mixed = json.dumps({"genre": "system",
                        "atoms": {"m": {"status": "Z"}},
                        "sentences": {"g": "or(Tr(m), not(Tr(m)))"}})
    d6, p6, _ = zfl.validate(mixed)
    rep6 = engine.run(d6, p6)
    k6 = {p["kind"] for p in rep6["passports"]}
    check("unverified input → INPUT + DOWNSTREAM",
          k6 == {"INPUT", "DOWNSTREAM"}, str(k6))

    print(f"\nTotal: {OK} ok, {FAIL} failed"
          + (" — ZFL FOUNDATION GREEN" if FAIL == 0 else ""))
    if FAIL:
        raise SystemExit(1)
