# -*- coding: utf-8 -*-
"""
ZFL v2 end to end, with no browser in the way.

The studio is the point of this work, but a language that can only be
exercised through a web page is a language nobody can test. Everything the
form will do — validate a cell, assemble the sheet, decide which
instruments apply, run them — happens here first, headless and under
assert, so the UI can be a view over something already known to work rather
than the only place it works at all.

Run:  python3 tool/test_zfl.py
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import zfl                                                      # noqa: E402

MIXED = {
    "rows": [
        {"name": "line", "means": "the invoice line", "status": "verified",
         "ground": "inv-17", "value": "1500", "unit": "RUB"},
        {"name": "budget", "means": "the ceiling", "status": "verified",
         "ground": "order-4", "value": "5000", "unit": "RUB"},
        {"name": "rain", "means": "it is raining", "status": "unverified"},
        {"name": "L", "means": "this sentence is false", "status": "defined",
         "ground": "~Tr(L)"},
    ],
    "claim": "line <= budget",
}


def sec1_one_table_three_instruments():
    print("-" * 72)
    print("1. ONE TABLE, AND NOBODY DECLARED A GENRE")
    r = zfl.run(MIXED)
    assert r["ok"], r["issues"]
    print(f"   applies: {r['applies']}")
    assert r["applies"] == {"numeric": True, "passport": True,
                            "ledger": True, "epoch": False, "judge": True,
                            "degree": False}
    rep = r["report"]
    print(f"   assembled sheet    : {rep['numeric']['sheet']}")
    print(f"   the invoice claim  : {rep['numeric']['disposition']}")
    print(f"   the liar row       : {rep['passport'][0]['kind']} "
          f"({rep['passport'][0]['detail'][:38]}…)")
    assert rep["numeric"]["disposition"] == "EARNED"
    assert rep["passport"][0]["kind"] == "PARADOX"
    print("   Four rows in one table, and two instruments answered without")
    print("   being chosen: the numeric floor compared roubles to roubles,")
    print("   the passport office convicted the liar. In v1 these were two")
    print("   genres, two tabs, and a declaration the writer had to get")
    print("   right before writing anything.")


def sec2_the_cells_are_checked_where_the_eye_is():
    print("-" * 72)
    print("2. ERRORS ADDRESSED TO A CELL, NOT TO A JSON PATH")
    bad = {"rows": [
        {"name": "a", "status": "verified"},
        {"name": "a", "status": "nonsense"},
        {"name": "L", "status": "defined", "ground": "~Tr(nowhere)"},
    ], "claim": "a <= budget"}
    issues = zfl.validate(bad)
    for i in issues:
        if i["level"] == "error":
            print(f"   {i['code']:16} {i['where']:18} {i['hint'][:44]}")
    codes = {i["code"] for i in issues}
    assert {"E_NOGROUND", "E_DUPNAME", "E_STATUS", "E_UNKNOWN_NAME"} <= codes
    print("   A verified name with nothing backing it, a duplicate, a status")
    print("   outside the four, a formula naming a row that does not exist —")
    print("   each answered at the cell the person is looking at. The typo")
    print("   in a name matters most: it is the commonest way to ask a")
    print("   perfectly well-formed question about nothing at all.")


def sec3_the_ledger_appears_when_it_is_wanted():
    print("-" * 72)
    print("3. TODAY'S LEDGER, REACHED FROM THE SAME TABLE")
    doc = {"rows": [
        {"name": "fee", "means": "the fee", "status": "verified",
         "ground": "cert-7", "ground_kind": "certificate", "value": "100"},
        {"name": "base", "means": "the base", "status": "verified",
         "ground": "deed", "value": "80"},
    ], "claim": "base <= fee"}
    r = zfl.run(doc)
    assert r["ok"], r["issues"]
    led = r["report"]["ledger"]
    print(f"   applies: {r['applies']}")
    for cid, v in led["claims"].items():
        print(f"   {cid:6} {v['disposition']:8} {v['assurance']}")
    print(f"   brackets: {led['brackets']}")
    print(f"   {led['naming']['assumption']}")
    assert r["applies"]["ledger"]
    assert led["claims"]["fee"]["assurance"]["under_expiry"] == "exposed"
    assert led["claims"]["base"]["assurance"]["under_expiry"] == "plain"
    print("   One dropdown — 'kind of ground: certificate' — and the whole")
    print("   of this morning's work arrives: the assurance frame, the trust")
    print("   brackets, the naming assumption printed beside them. The user")
    print("   never learns a syntax for any of it.")


def sec3b_what_the_ground_column_is_actually_for():
    print("-" * 72)
    print("3b. WHY THE GROUND NAME IS NOT DECORATION")
    apart = {"rows": [
        {"name": "a", "means": "first line", "status": "verified",
         "ground": "inv-17", "value": "100"},
        {"name": "b", "means": "second line", "status": "verified",
         "ground": "inv-18", "value": "200"}]}
    same = {"rows": [dict(apart["rows"][0]),
                     dict(apart["rows"][1], ground="inv-17")]}
    ia = zfl.run(apart)["report"]["ledger"]["brackets"]
    isame = zfl.run(same)["report"]["ledger"]["brackets"]
    print(f"   two lines on two documents : {ia}")
    print(f"   two lines on ONE document  : {isame}")
    assert ia == {"inv-17": [1, 1], "inv-18": [1, 1]}
    assert isame == {"inv-17": [2, 2]}
    print("   That is the whole answer to 'the ground column says nothing'.")
    print("   The name is opaque — the machine never looks inside it — but")
    print("   its IDENTITY is load-bearing: put two lines on one invoice and")
    print("   losing it costs two claims instead of one. Nothing else in the")
    print("   table can say that, and `means` certainly cannot: a gloss is")
    print("   for the reader, a ground is what the arithmetic of collapse")
    print("   runs on.")


def sec4_an_unknown_is_a_question_not_a_gap():
    print("-" * 72)
    print("4. ASKING FOR A NUMBER, WHICH IS WHAT PEOPLE ACTUALLY WANT")
    for claim in ("x - 10 = 20", "x - 10 == 20", "sum(x,x) = 60",
                  "-x + 100 = 70"):
        doc = {"rows": [{"name": "x", "means": "the unknown",
                         "status": "unverified", "value": "?"}],
               "claim": claim}
        r = zfl.run(doc)
        assert r["ok"], r["issues"]
        n = r["report"]["numeric"]
        sv = n["solved"]["x"]
        print(f"   {claim:16} -> {n['disposition']:8} x = {sv['lo']}"
              f"  ({sv['prov']})")
        assert n["disposition"] == "EARNED" and sv["lo"] == "30"
        # the last one carries a UNARY minus, which the arithmetic reader
        # could not parse until the curator asked it to solve an equation
        # that opened with one
        assert sv["pinned"] and sv["prov"] == "earned"
    print("   `x=?` in the table is a QUESTION, not a missing cell, so the")
    print("   solver answers it — and answers with the provenance the value")
    print("   inherited from the derivation. Judging alone would have said")
    print("   'measure x', which is true and useless when the sheet already")
    print("   determines it.")
    print("   And a lone `=` is read as equality wherever the document has")
    print("   quantities. `x - 10 = 20` is what a person writes; making them")
    print("   type `==` would be the machine's convenience charged to them.")


def sec13_naive_sets_are_in_the_language():
    print("-" * 72)
    print("13. NAIVE SETS IN THE LANGUAGE (2026-11-05): cells become rows, the passport reads them")
    import time
    import znaive
    russell = {"rows": [], "sets": {"a": {"list": []}, "b": {"list": ["b"]},
                                    "R": {"abs": ["not", ["in", "x", "x"]]}}}
    r = zfl.run(dict(russell, claim="in(a, R) & ~in(b, R)"))
    assert r["ok"] and r["report"]["judge"]["disposition"] == "EARNED", r
    assert [(p["component"], p["kind"]) for p in r["report"]["passport"]] == [(["R_in_R"], "PARADOX")], r
    r = zfl.run(dict(russell, claim="R_in_R"))
    assert r["ok"] and r["report"]["judge"]["disposition"] == "OPEN", r["report"]["judge"]
    # the same verdicts as the kernel's own naive judge, on every cell of its four universes
    for name, ex in znaive.EXAMPLES.items():
        nv = znaive.check(ex)
        for st in nv["sets"]:
            for m in st["in"] + st["out"] + [q["member"] for q in st["quarantined"]]:
                cl = f"{m}_in_{st['set']}"
                rz = zfl.run({"rows": [], "sets": ex, "claim": cl})
                assert rz["ok"], (name, cl, rz["issues"])
                v = rz["report"]["judge"]["verdict"]
                want = "T" if m in st["in"] else "F" if m in st["out"] else "Z"
                assert v == want, (name, cl, v, want)
                if want == "Z":
                    kinds = {c: p["kind"] for p in rz["report"]["passport"] for c in p["component"]}
                    want_kind = next(q["passport"] for q in st["quarantined"] if q["member"] == m)
                    # an INPUT cell no definition reads is, in ZFL, simply an unverified row (no system to join)
                    plain_input = (want_kind == "INPUT" and cl not in kinds and any(
                        r_["name"] == cl and r_["status"] == "unverified" for r_ in zfl.coerce(
                            {"rows": [], "sets": ex, "claim": cl})["rows"]))
                    assert plain_input or kinds.get(cl) == want_kind or want_kind == "DOWNSTREAM", \
                        (name, cl, kinds.get(cl), want_kind)
    # the door: refusals are issues on `sets`, at once; coerce twice adds nothing twice
    deep = ["in", "x", "x"]
    for v in "abcdef":
        deep = ["all", v, ["or", ["in", v, "x"], deep]]
    t0 = time.time()
    for bad in ({"T": {"list": []}}, {"A": {"abs": ["in", "x", "ghost"]}}, "{not json",
                {f"s{i}": {"abs": deep} for i in range(8)}, {"abs": {"list": []}}):
        r = zfl.run({"rows": [], "sets": bad, "claim": "p"})
        assert not r["ok"] and "E_SETS" in [i["code"] for i in r["issues"]], (bad, r["issues"])
    assert time.time() - t0 < 2
    r = zfl.run({"rows": [{"name": "A_in_A", "means": "m", "status": "unverified"}],
                 "sets": {"A": {"list": []}}, "claim": "A_in_A"})
    assert not r["ok"] and "E_SETS" in [i["code"] for i in r["issues"]]
    d = zfl.coerce(dict(russell, claim="R_in_R"))
    assert len(zfl.coerce(d)["rows"]) == len(d["rows"]) == 3, d["rows"]
    # a person's own defined row may lean on a cell
    r = zfl.run({"rows": [{"name": "ok", "means": "a is in R and paid", "status": "defined",
                           "ground": "in(a, R) & paid"},
                          {"name": "paid", "means": "paid", "status": "verified", "ground": "inv-1"}],
                 "sets": russell["sets"], "claim": "ok"})
    assert r["ok"] and r["report"]["judge"]["verdict"] == "T", r
    print("   Russell's set: a ∈ R and b ∉ R EARNED, R ∈ R a PARADOX through the same passport as the Liar;")
    print("   every cell of znaive's four example universes reads the same in ZFL (T/F/Z and the passport);")
    print("   bad names, unknown names, broken JSON, an oversized universe, a name clash: E_SETS, at once.")

def sec22_a_system_with_sin_cos_tan_in_a_search_region():
    """(2026-11-08, the curator: "sin/cos в ZFL — не забудь"; "если знаешь как улучшить — делай") Systems with the
    trigonometric functions, judged by the same exact readings (zfunc's sin/cos with ztrigcert's Lean witnesses).
    Both sides: the circle meets y = sin 2x twice in [-2, 2]² — COMPLETE, both checked in floats; y = tan x,
    x + y = 1 over a region holding pi/2 (where cos = 0) — not exhausted, the solution found stays LOCAL; the circle
    only TOUCHES y = cos x at (0, 1) (a singular Jacobian: no cube can be certified, no box near it excluded) —
    OPEN, nothing claimed, said as searched (W_REGION_UNUSED's second meaning). MEASURED 2026-11-08: the sin system
    took 30 s (exact sin/cos readings in Newton's steps, Fraction's gcd); with Newton in floats (zsystem._ff, a
    proposal only) and the series in integers (zfunc._sc_series, ztrigcert.cert) 0.12 s; the touching case > 10 min
    before, 1.8 s now."""
    import math
    from fractions import Fraction
    print("-" * 72)
    print("§22 a system with sin, cos, tan in a search region")
    U = lambda n, v="?": {"name": n, "means": n, "status": "unverified", "value": v}
    R = lambda: [U("x", "? in [-2, 2]"), U("y", "? in [-2, 2]")]
    r = zfl.run({"rows": R(), "claim": "x*x + y*y = 1 & y = sin(2*x)"})
    n = r["report"]["numeric"]
    assert n["disposition"] == "EARNED" and n["system"]["complete"] and n["system"]["solutions"] == 2, n
    assert any(i["code"] == "W_SYSTEM_ALL" for i in r["issues"])
    for c in n["system"]["certificates"]:
        x, y = (float(Fraction(v)) for v in c["centre"])
        assert abs(x * x + y * y - 1) < 1e-6 and abs(y - math.sin(2 * x)) < 1e-6, (x, y)
    print("   the circle meets y = sin 2x in [-2,2]²: COMPLETE, 2 solutions, each checked in floats")
    r = zfl.run({"rows": R(), "claim": "y = tan(x) & x + y = 1"})
    n = r["report"]["numeric"]
    assert n["disposition"] == "EARNED" and not n["system"]["complete"], n
    assert any(i["code"] == "W_SYSTEM_LOCAL" for i in r["issues"])
    assert not any(i["code"] == "W_SYSTEM_ALL" for i in r["issues"])
    print("   y = tan x, x + y = 1 over a region holding pi/2: a LOCAL answer, no complete claim")
    r = zfl.run({"rows": R(), "claim": "x*x + y*y = 1 & y = cos(x)"})
    n = r["report"]["numeric"]
    assert n["disposition"] == "OPEN", n
    w = [i for i in r["issues"] if i["code"] == "W_REGION_UNUSED"]
    assert w and "searched but not exhausted" in w[0]["hint"], r["issues"]
    print("   the circle touching y = cos x at (0, 1): OPEN, said as searched, nothing claimed")


def sec23_one_unknown_in_a_search_region():
    """(2026-11-08, the curator's order: the weaknesses first) ONE unknown with its region `x = ? in [a, b]` and one
    equation, where the exact solver PROVED nothing: the region is exhausted the same way as a system's (zsystem,
    d = 1) and the answer is COMPLETE. Both sides: x = cos x in [0, 2] — the one root (Dottie's number), checked in
    floats; x·eˣ = 1 in [0, 3] — the omega constant; x³ − 2x = 0.1 in [−4, 4] — THREE certified intervals where the
    solver had only `≈` approximations; x = cos x in [2, 3] — none, REFUTED; an exact answer (x² = 2 -> ±√2) is kept
    and the region said unused; without a region x = cos x stays OPEN (nothing claimed). Sabotage: a forged interval
    that misses the root is refused by the exact check."""
    import math
    from fractions import Fraction
    import zsystem
    print("-" * 72)
    print("§23 one unknown in a search region")
    U = lambda n, v="?": {"name": n, "means": n, "status": "unverified", "value": v}

    def roots(v, claim):
        r = zfl.run({"rows": [U("x", v)], "claim": claim})
        n = r["report"]["numeric"]
        bx = [tuple(Fraction(t) for t in b.strip("[]").split(", ")) for b in ((n.get("solved") or {}).get("x") or {})
              .get("roots", []) if b.startswith("[")]
        return r, n, bx
    r, n, bx = roots("? in [0, 2]", "x = cos(x)")
    assert n["disposition"] == "EARNED" and n["system"]["complete"] and len(bx) == 1, n
    assert any(i["code"] == "W_SYSTEM_ALL" for i in r["issues"])
    c = float(sum(bx[0]) / 2)
    assert abs(c - math.cos(c)) < 1e-9 and bx[0][1] - bx[0][0] < Fraction(1, 10 ** 5), bx
    r, n, bx = roots("? in [0, 3]", "x*exp(x) = 1")
    assert n["disposition"] == "EARNED" and len(bx) == 1 and abs(float(sum(bx[0]) / 2) - 0.5671432904) < 1e-8, n
    r, n, bx = roots("? in [-4, 4]", "x*x*x - 2*x = 0.1")
    assert n["disposition"] == "EARNED" and n["system"]["complete"] and len(bx) == 3, n
    for b in bx:
        c = float(sum(b) / 2)
        assert abs(c ** 3 - 2 * c - 0.1) < 1e-9, bx
    print("   x = cos x in [0,2]: one root ~0.739085; x·eˣ = 1: omega; x³ − 2x = 0.1: three certified intervals")
    r, n, bx = roots("? in [2, 3]", "x = cos(x)")
    assert n["disposition"] == "REFUTED" and n["verdict"] == "F", n
    r, n, bx = roots("? in [0, 10]", "x*x = 2")
    assert n["disposition"] == "EARNED" and n["solved"]["x"]["roots"] == ["-√2", "√2"], n
    assert any(i["code"] == "W_REGION_UNUSED" for i in r["issues"])
    r, n, bx = roots("?", "x = cos(x)")
    assert n["disposition"] == "OPEN" and not bx, n
    print("   none in [2,3]: REFUTED; the exact ±√2 kept (region unused, said); no region: OPEN")
    import znumjudge as ZJ
    qs = ZJ.parse_quantities("x=? credit")[0]
    law = [ZJ._parse_arith("(x) - (cos(x))", qs)]
    forged = {"centre": ["1"], "radius": "1/1024", "Y": [["1/2"]], "Z": [["2"]]}
    assert not zsystem.check(law, ["x"], qs, forged)[0]
    print("   sabotage: a forged interval around 1 (the root is ~0.739) is refused by the exact check")


def sec4b_every_example_runs_and_json_types_are_taken_as_they_come():
    print("-" * 72)
    print("4b. THE CATALOGUE, AND WHAT ARRIVES FROM A MODEL")
    import zflexamples as X
    kinds = {}
    for e in X.EXAMPLES:
        r = zfl.run(e["doc"])
        assert r["ok"], (e["en"], r["issues"])
        kinds.setdefault(e["kind"], 0)
        kinds[e["kind"]] += 1
    print(f"   {len(X.EXAMPLES)} examples, all validating and running: {kinds}")
    # (The published-docket cross-check — that the studio's own example set
    # holds every case the paradox paper names — lives in the studio repo now,
    # ztlstudio, where ztlstudio.EXAMPLES is defined. Here we check the
    # language's own catalogue, which travels with zfl.)
    assert set(kinds) == set(X.KINDS)
    print("   An example is a promise about the machine, so a broken one may")
    print("   not ship. This caught a real crash on the first run: a row with")
    print("   value `?` was being turned into the ledger claim `b == ?`,")
    print("   which the sheet parser rightly refused — a question is not a")
    print("   claim about a value.")
    # a model writes JSON, and JSON has JSON's types
    doc = {"rows": [{"name": "a", "means": "x", "status": "verified",
                     "ground": "inv-1", "value": 3000, "unit": "RUB"},
                    {"name": "cap", "means": "y", "status": "verified",
                     "ground": "c", "value": 5000, "unit": "RUB"}],
           "claim": "a <= cap"}
    r = zfl.run(doc)
    print(f"   values arriving as NUMBERS: {r['report']['numeric']['sheet']}")
    assert r["ok"] and r["report"]["numeric"]["disposition"] == "EARNED"
    print("   `\"value\": 3000` is not wrong of a model or of a caller, and it")
    print("   crashed the validator the first time the AI filled the table.")
    print("   Types are coerced once at the door instead of defensively in")
    print("   twenty places.")


def sec5_the_spec_can_build_the_form_and_the_page():
    print("-" * 72)
    print("5. ONE SPEC BEHIND THE FORM, THE VALIDATOR AND THE PAGE")
    for lang in ("en", "ru"):
        spec = zfl.form_spec(lang)
        cols = spec["columns"]
        assert len(cols) == len(zfl.COLUMNS)
        assert all(c["label"] and c["help"] for c in cols)
        widgets = sorted({c["widget"] for c in cols})
        print(f"   {lang}: {len(cols)} columns, widgets {widgets}")
        for c in cols:
            if c["widget"] in ("choice", "multi"):
                assert c["options"] and all(o["label"] for o in c["options"])
    req = [c["key"] for c in zfl.form_spec()["columns"] if c["required"]]
    cond = [c["key"] for c in zfl.form_spec()["columns"]
            if c["required_when"]]
    print(f"   always required: {req}   required in context: {cond}")
    assert req == ["name", "status"] and cond == ["ground"]
    print("   The widget follows from the column's TYPE, so a dropdown, a")
    print("   toggle and a stepper are not decisions the front-end makes —")
    print("   they are read off the same table that the validator enforces")
    print("   and the reference page will describe. Add a column here and")
    print("   it appears in all three, or in none of them.")




def sec7_the_ground_gate_demotes_phantom_words():
    """Ворота оснований (2026-08-27). Три инварианта, каждый — прогон:
    без реестра поведение прежнее; слово-фантом при реестре НЕ зарабатывает
    и падает в кредит, поимённо; настоящее основание из реестра стоит."""
    print("\n### 7. The ground gate: a phantom word must not earn")
    doc = {"rows": [
        {"name": "p", "means": "x", "status": "verified",
         "ground": "СЛОВО-ФАНТОМ"},
        {"name": "q", "means": "y", "status": "verified", "ground": "inv-17"}],
        "claim": "p & q"}
    a = zfl.run(doc)
    ja = a["report"]["judge"]
    assert (ja["verdict"], ja["grade"]) == ("T", "hereditary")
    assert "demoted_grounds" not in a["report"]          # без реестра — как раньше
    b = zfl.run(doc, ground_registry={"inv-17"})
    jb = b["report"]["judge"]
    assert jb["verdict"] == "F" and jb["disposition"] == "OPEN"
    assert b["report"]["demoted_grounds"] == ["p"]       # поимённо
    c = zfl.run({"rows": [doc["rows"][1]], "claim": "q"},
                 ground_registry={"inv-17"})
    jc = c["report"]["judge"]
    assert (jc["verdict"], jc["grade"]) == ("T", "hereditary")
    print("   without a registry: byte-identical behaviour;")
    print("   with one: the phantom is demoted BY NAME and the verdict")
    print("   honestly falls OPEN; a registered ground still earns.")

def sec8_the_credit_that_cannot_be_redeemed():
    """The judge and the passport stop contradicting each other.

    Found 2026-08-28 marking up Protagoras v. Euathlus: one report said
    `until-verification` ("go and check") about the very name the passport
    called a PERMANENT refusal ("there is nothing to check, ever"). Three
    invariants here — the mark appears where the ring is dead, it does NOT
    appear on an ordinary dirty atom, and the verdict itself is
    untouched (the core computed it correctly; only what the marking could
    not say is added beside it)."""
    print("\n### 8. a credit that cannot be redeemed says so")

    liar = {"claim": "L", "rows": [
        {"name": "L", "means": "this sentence is false",
         "status": "defined", "ground": "~Tr(L)"}]}
    j = zfl.run(liar)["report"]["judge"]
    assert j["credit"] == "UNREDEEMABLE", j
    assert j["unredeemable"] == ["L"], j
    assert j["grade"] == "until-verification", j      # the grade is NOT rewritten
    assert j["verdict"] == "Z", j                     # nor the verdict
    print("   the liar: grade untouched, credit marked UNREDEEMABLE")

    # An ordinary dirty atom is a real credit — it must NOT be marked.
    plain = {"claim": "p", "rows": [
        {"name": "p", "means": "the cat lives next door",
         "status": "unverified", "ground": ""}]}
    j2 = zfl.run(plain)["report"]["judge"]
    assert "credit" not in j2, j2
    print("   an ordinary mark is left alone — no false positive")

    # A grounded definition is completable: no mark either.
    grounded = {"claim": "g", "rows": [
        {"name": "seen", "means": "checked", "status": "verified",
         "ground": "logbook"},
        {"name": "g", "means": "g is what was seen",
         "status": "defined", "ground": "Tr(seen)"}]}
    j3 = zfl.run(grounded)["report"].get("judge") or {}
    assert "credit" not in j3, j3
    print("   a grounded definition is completable — no mark")


def sec9_the_world_has_a_clock_too():
    """The epoch floor: a conclusion resting on a clocked ground loses it.

    Every other column speaks of what is KNOWN; `expires_on` speaks of what
    stops being true. ZTL has carried the distinction since E25 and proves
    it in `EpochBoundary.lean`, but the table could not say it, so a
    temporal case had to be staged by hand in Python (Protagoras v.
    Euathlus, 2026-08-28). Three invariants: the crossing is computed, it
    is computed THROUGH the definitions, and a document with no clock is
    left exactly as it was."""
    print("\n### 9. the world has a clock, and the table can say so")

    car = {"claim": "deal_ok", "rows": [
        {"name": "registry_recheck", "means": "the pledge registry is re-read",
         "status": "unverified", "ground": ""},
        {"name": "pledge_free", "means": "not pledged", "status": "verified",
         "ground": "registry_extract", "expires_on": "registry_recheck"},
        {"name": "papers_ok", "means": "papers in order", "status": "verified",
         "ground": "vehicle_title"},
        {"name": "deal_ok", "means": "the deal may close", "status": "defined",
         "ground": "Tr(pledge_free) & Tr(papers_ok)"}]}
    e = zfl.run(car)["report"]["epoch"][0]
    assert e["event"] == "registry_recheck" and e["expires"] == ["pledge_free"]
    assert e["before"] == {"verdict": "T", "grade": "hereditary"}, e
    assert e["after"]["verdict"] == "Z", e
    assert e["survives"] is False, e
    print("   the purchased car: T/hereditary before, Z after — did NOT survive")

    # THROUGH the definitions: `deal_ok` is a defined row, and reading the
    # marking alone would have shown Z on both sides and called it survival.
    assert e["before"]["verdict"] != e["after"]["verdict"]
    print("   and it is read through the definition, not around it")

    # An event nobody declared cannot be staged.
    bad = {"claim": "a", "rows": [
        {"name": "a", "means": "x", "status": "verified", "ground": "doc",
         "expires_on": "nowhere"}]}
    codes = {i["code"] for i in zfl.run(bad)["issues"]}
    assert "E_UNKNOWN_NAME" in codes, codes
    # Only ground can expire — a mark has nothing for the clock to take.
    bad2 = {"claim": "a", "rows": [
        {"name": "ev", "means": "e", "status": "unverified", "ground": ""},
        {"name": "a", "means": "x", "status": "unverified", "ground": "",
         "expires_on": "ev"}]}
    codes2 = {i["code"] for i in zfl.run(bad2)["issues"]}
    assert "E_EXPIRY_NO_GROUND" in codes2, codes2
    print("   an undeclared event and an expiring mark are both refused")

    # A document with no clock is untouched: no floor, no key.
    plain = {"claim": "a", "rows": [
        {"name": "a", "means": "x", "status": "verified", "ground": "doc"}]}
    r = zfl.run(plain)
    assert r["applies"]["epoch"] is False and "epoch" not in r["report"]
    print("   a document with no clock is left exactly as it was")


def sec10_what_the_ground_holds_and_what_to_check():
    """After the verdict, the report says what each ground holds and how it
    came out, and — for a claim still resting on dirty inputs — which
    of them to check, by GUARANTEE and by POSSIBILITY (2026-09-24)."""
    print("\n### 10. What the ground holds, and what to check")
    yablo = {"rows": [
        {"name": "s0", "means": "none after is true", "status": "defined", "ground": "~Tr(s1) & ~Tr(s2)"},
        {"name": "s1", "means": "none after is true", "status": "defined", "ground": "~Tr(s2)"},
        {"name": "s2", "means": "none after is true", "status": "verified", "ground": "story"}]}
    rows = zfl.run(yablo)["report"]["passport_rows"]
    assert {n: (v["kind"], v["value"]) for n, v in rows.items()} == {
        "s0": ("GROUNDED", "F"), "s1": ("GROUNDED", "F"), "s2": ("GROUNDED", "T")}, rows
    assert rows["s0"]["reads"] == ["s1", "s2"] and rows["s2"]["reads"] == [], rows
    liar = {"rows": [{"name": "L", "means": "this is false", "status": "defined", "ground": "~Tr(L)"}]}
    assert zfl.run(liar)["report"]["passport_rows"]["L"] == {"kind": "PARADOX", "value": "Z", "reads": ["L"]}

    def unverified(claim, *names):
        return {"claim": claim, "rows": [{"name": n, "means": n, "status": "unverified"} for n in names]}
    rep = zfl.run(unverified("p | ~p", "p"))["report"]
    w = rep["what_to_check"]
    assert w["EARNED"]["guaranteed"] == [["p"]], w
    assert w["REFUTED"]["no_possible_set"] is True, w
    assert rep["judge"]["why"], rep["judge"]
    w = zfl.run(unverified("p & (q | r)", "p", "q", "r"))["report"]["what_to_check"]
    assert w["EARNED"]["possible"] == [["p", "q"], ["p", "r"]] and w["EARNED"]["no_guaranteed_set"], w
    w = zfl.run(unverified("a & b & c & d & e & f & g", *"abcdefg"))["report"]["what_to_check"]
    assert "refused" in w and "up to 3" in w["refused"], w
    settle = {"claim": "signed & delivered", "rows": [
        {"name": "signed", "means": "signed", "status": "verified", "ground": "scan-12"},
        {"name": "delivered", "means": "arrived", "status": "unverified"}]}
    w = zfl.run(settle)["report"]["what_to_check"]
    assert w["SETTLED"]["guaranteed"] == [["delivered"]], w      # one check closes it, either way
    assert w["EARNED"]["no_guaranteed_set"] and w["EARNED"]["possible"] == [["delivered"]], w
    done = {"claim": "p", "rows": [{"name": "p", "means": "p", "status": "verified", "ground": "doc"}]}
    assert "what_to_check" not in zfl.run(done)["report"]
    print("   every defined row reports its kind, value and what it reads;")
    print("   a claim on unverified inputs reports what to check, by guarantee")
    print("   and by possibility, says so when no set will do, and refuses")
    print("   above six inputs rather than spending seconds per request.")


def sec11_a_public_service_cannot_be_made_to_raise_or_to_stall():
    """Found by probing the public API (2026-09-24): a value past float range
    made run() raise from the ledger branch (the service answered 500), and a
    long product chain took seconds, the readers being quadratic in length."""
    import time
    print("\n### 11. A public service cannot be made to raise or to stall")
    # The atom cap counts what the core READS (2026-09-26). A comparison is an
    # atom (one name, fourteen comparisons cost seconds); a witness label on a
    # non-defined row is not (introspect's `san-guard-filter_var-...-L48` read
    # as five atoms refused 1 080 SARD documents).
    # (2026-09-27: comparisons are capped on their own at 16, plain atoms at 10)
    for n, capped in ((16, False), (17, True)):
        chain = {"claim": " ^ ".join(f"(x <= {j})" for j in range(1, n + 1)),
                 "rows": [{"name": "x", "means": "x", "status": "unverified", "value": "[0,50]"}]}
        got = any(i["code"] == "E_TOOBIG" for i in zfl.validate(chain))
        assert got == capped, f"{n} comparisons: capped={got}, want {capped}"
    labels = {"claim": "safe", "rows": [
        {"name": "tainted", "ground_kind": "act", "status": "verified", "ground": "src-_GET-L45", "means": "t"},
        {"name": "sanitized", "ground_kind": "act", "status": "verified",
         "ground": "san-guard-filter_var-FILTER_VALIDATE_FLOAT-L48", "means": "s"},
        {"name": "safe", "status": "defined", "ground": "~Tr(tainted) | Tr(sanitized)", "means": "c"}]}
    assert not any(i["code"] == "E_TOOBIG" for i in zfl.validate(labels)), "witness labels are not atoms"
    print("   the cap counts comparisons, not witness labels: ok")
    # 2026-09-29: plain atoms are capped by REPEATS (10), all atoms at 64. The exact
    # guarantee branches only on atoms named twice (zverify._only); E57 puts the
    # hardness there. MEASURED in ztlstudio a78db5a (40 read-once atoms < 0.01 s;
    # 30 repeated in guard -> ~PHP(6,5), 0.66 s).
    def _rows(ns):
        return [{"name": n, "means": n, "status": "unverified"} for n in ns]
    once = [f"a{i}" for i in range(40)]
    assert not any(i["code"] == "E_TOOBIG" for i in zfl.validate(
        {"claim": " & ".join(once), "rows": _rows(once)})), "40 atoms named once are not capped"
    rep = [f"b{i}" for i in range(11)]
    assert any(i["code"] == "E_TOOBIG" for i in zfl.validate(
        {"claim": " & ".join(f"({x} | ~{x})" for x in rep), "rows": _rows(rep)})), "11 repeated are capped"
    assert not any(i["code"] == "E_TOOBIG" for i in zfl.validate(
        {"claim": " & ".join(f"({x} | ~{x})" for x in rep[:10]), "rows": _rows(rep[:10])})), "10 repeated pass"
    many = [f"c{i}" for i in range(65)]
    assert any(i["code"] == "E_TOOBIG" for i in zfl.validate(
        {"claim": " & ".join(many), "rows": _rows(many)})), "65 distinct are capped"
    print("   plain atoms: 10 REPEATED, 64 in all (read-once ones cost nothing): ok")
    big = {"claim": "*".join(["a"] * 200) + " > b", "rows": [
        {"name": "a", "means": "a", "status": "verified", "ground": "doc", "value": "1" + "0" * 1000},
        {"name": "b", "means": "b", "status": "verified", "ground": "doc", "value": "1"}]}
    r = zfl.run(big)                       # raised OverflowError until this date
    assert r["ok"] is False and any(i["code"] == "E_UNREADABLE" for i in r["issues"]), r
    rows = [{"name": "a", "means": "a", "status": "verified", "ground": "doc", "value": "2"},
            {"name": "b", "means": "b", "status": "verified", "ground": "doc", "value": "1"}]
    long_claim = "*".join(["a"] * 2500) + " > b"
    codes = [(i["code"], i["where"]) for i in zfl.run({"claim": long_claim, "rows": rows})["issues"]]
    assert ("E_TOOLONG", "claim") in codes, codes
    long_ground = [{"name": "s", "means": "s", "status": "defined", "ground": " & ".join(["~Tr(s)"] * 800)}]
    codes = [(i["code"], i["where"]) for i in zfl.run({"rows": long_ground})["issues"]]
    assert ("E_TOOLONG", "row 1") in codes, codes
    near = "*".join(["a"] * 995) + " > b"             # just under the cap (2000 since 2026-09-27)
    t0 = time.time()
    r = zfl.run({"claim": near, "rows": rows})
    assert "E_TOOLONG" not in [i["code"] for i in r.get("issues", [])] and time.time() - t0 < 2.0, r
    print("   a value past float range is an issue, not a traceback; a formula")
    print("   over 2000 characters is refused by name; one under it reads fast.")


def sec15_a_convention_changes_the_order_never_the_verdict():
    """(2026-11-05) The `convention` column. Both sides: on a battery of documents the numeric disposition and polarity
    are the same with and without it, and the cures differ only measure <-> stipulate for that row; an empirical row
    beside it keeps 'measure'; a convention with 'sample' or without a value is refused (E_CONVENTION). Sabotage: a
    to_sheet that drops the token must break the cure check."""
    import copy
    print("-" * 72)
    print("§15 a convention changes the order, never the verdict")
    docs = [
        ({"rows": [{"name": "P", "status": "verified", "ground": "methods", "value": "[1/4,1/2]"}]}, "P == 1/2"),
        ({"rows": [{"name": "P", "status": "verified", "ground": "methods", "value": "[1/4,1/2]"}]}, "P >= 1/4"),
        ({"rows": [{"name": "P", "status": "unverified", "value": "[1/4,1/2]"}]}, "P > 1/2"),
        ({"rows": [{"name": "P", "status": "verified", "ground": "methods", "value": "[1/4,1/2]"},
                   {"name": "n", "status": "verified", "ground": "count", "value": "[30,50]"}]}, "P * n >= 10"),
    ]
    for doc, claim in docs:
        plain = copy.deepcopy(doc); plain["claim"] = claim
        conv = copy.deepcopy(plain); conv["rows"][0]["convention"] = True
        a, b = zfl.run(plain)["report"]["numeric"], zfl.run(conv)["report"]["numeric"]
        assert (a["disposition"], a.get("polarity")) == (b["disposition"], b.get("polarity")), (claim, a, b)
        assert [c.replace("measure P", "stipulate P") for c in a["next_check"]] == b["next_check"], (claim, a, b)
    both = {"rows": [{"name": "P", "status": "verified", "ground": "methods", "value": "[1/4,1/2]", "convention": True},
                     {"name": "n", "status": "verified", "ground": "count", "value": "[30,50]"}], "claim": "P * n >= 10"}
    cures = zfl.run(both)["report"]["numeric"]["next_check"]
    assert "stipulate P" in cures and "measure n" in cures, cures
    for bad in ({"rows": [{"name": "P", "status": "unverified", "value": "[0,1]", "convention": True, "sample": True}],
                 "claim": "P > 0"},
                {"rows": [{"name": "q", "status": "unverified", "convention": True}], "claim": "q"}):
        assert any(i["code"] == "E_CONVENTION" for i in zfl.validate(bad)), bad
    real = zfl.to_sheet
    zfl.to_sheet = lambda rows: real(rows).replace(" convention", "")         # sabotage: the token never travels
    try:
        assert "stipulate P" not in zfl.run(both)["report"]["numeric"]["next_check"]
    finally:
        zfl.to_sheet = real
    print("   same verdict with and without the column; 'stipulate' for the convention, 'measure' beside it;")
    print("   convention + separate measurements, or a convention with no value: E_CONVENTION; sabotage caught")


def sec16_a_lone_equals_is_read_by_the_types_of_its_sides():
    """(2026-11-05) `=` between numbers is numeric equality, between statements the biconditional, a statement against
    a number is refused (E_TYPE_EQ) — whatever else the document holds. Both sides: the equations of the catalogue
    read as before; `p = q` and `p = (x > 1)` are biconditionals even beside a quantity. Sabotage: the old
    per-document reading must fail the new cases."""
    print("-" * 72)
    print("§16 a lone '=' is read by the types of its sides")
    rows = [{"name": "p", "status": "unverified", "means": "a"}, {"name": "q", "status": "unverified", "means": "b"},
            {"name": "x", "status": "verified", "ground": "m", "value": "2", "means": "c"}]
    want = {"p = q": "p = q", "p = (x > 1)": "p = (x > 1)", "(x > 1) = p": "(x > 1) = p",
            "x = 2": "x == 2", "x - 1 = 1 & p": "x - 1 == 1 & p", "x * 3 = 6": "x * 3 == 6",
            "sum(x,x) = 4": "sum(x,x) == 4", "p = q & (x >= 1)": "p = q & (x >= 1)"}
    for c, n in want.items():
        assert zfl.normalise(c, rows) == n, (c, zfl.normalise(c, rows))
        assert zfl.run({"rows": rows, "claim": c})["ok"], c
    for c in ("p = x", "p = 5"):
        assert any(i["code"] == "E_TYPE_EQ" for i in zfl.validate({"rows": rows, "claim": c})), c
    # without any quantity a lone `=` between statements is the biconditional, as it always was
    assert zfl.normalise("p = q", rows[:2]) == "p = q"
    # verdicts: p = (x > 1) with x = 2 is p's own status; p = q over two Z rows is open
    r = zfl.run({"rows": rows, "claim": "p = (x > 1)"})["report"]
    assert r["numeric"]["disposition"] == "OPEN", r
    real = zfl.eq_kinds
    zfl.eq_kinds = lambda text, rows: [(m.start(), "unknown") for m in zfl._LONE_EQ.finditer(text)]   # sabotage
    try:
        assert zfl.normalise("p = q", rows) == "p == q"          # the old reading comes back ...
        assert not zfl.run({"rows": rows, "claim": "p = q"})["ok"]  # ... and the biconditional dies again
    finally:
        zfl.eq_kinds = real
    # whitespace inside a value is layout: "[0, 1]" reads as "[0,1]" (a blind formalization died three rounds on it)
    for v in ("[0, 1]", " [0 ,1] ", "[ 1/4 , 1/2 ]", [0, "inf"], ["1/4", "1/2"], [0, 10]):
        assert zfl.run({"rows": [{"name": "w", "status": "unverified", "value": v, "means": "m"}],
                        "claim": "w >= 0"})["ok"], v
    print("   numbers = numbers -> ==; statements = statements -> the biconditional, beside a quantity too;")
    print("   a statement = a number -> E_TYPE_EQ; the old per-document reading, as sabotage, is caught")


def sec17_a_clock_beside_a_numeric_claim_never_crashes():
    """(2026-11-05) A row with a clock (expires_on) and a claim that compares numbers made the time layer raise
    ("stray character '>'") on a document that had passed validation — a public service turning a question into an
    internal error. Now the time layer reads statements only and says so (W_EPOCH_NUMERIC); a statement claim beside
    a clock still gets the time layer. Both sides."""
    print("-" * 72)
    print("§17 a clock beside a numeric claim never crashes, and says what it did not read")
    rows = [{"name": "cert", "means": "a certificate", "status": "verified", "ground": "story", "ground_kind": "certificate",
             "expires_on": "cert_end"},
            {"name": "cert_end", "means": "the end", "status": "unverified"},
            {"name": "fee", "means": "fee", "status": "unverified", "value": "?"},
            {"name": "paid", "means": "paid", "status": "unverified", "value": "?"},
            {"name": "ok", "means": "covered", "status": "unverified"}]
    for c in ("paid >= fee", "paid >= fee & ok = (paid >= fee)"):
        r = zfl.run({"rows": rows, "claim": c})
        assert r["ok"] and "epoch" not in r["report"], (c, r.get("issues"))
        assert any(i["code"] == "W_EPOCH_NUMERIC" for i in r["issues"]), c
    for c in ("cert & ok", "cert -> ok"):
        r = zfl.run({"rows": rows, "claim": c})
        assert r["ok"] and "epoch" in r["report"], c
        assert not any(i["code"] == "W_EPOCH_NUMERIC" for i in r["issues"]), c
    print("   numeric claim + clock: no crash, the time layer named as not reading it; statements: the time layer reads")


def sec18_a_comparison_can_be_named():
    """(2026-11-05) A defined row whose ground compares numbers names that comparison: the claim reads it where the
    name stands. Both sides: named or written out, the same verdict; a loop and a self-reference definition leaning on
    a comparison row are refused (E_COMPARE_ROW); a liar with no comparison is still the passport office's. Sabotage:
    without the expansion the named form is refused again."""
    print("-" * 72)
    print("§18 a comparison can be named")
    base = [{"name": "x", "status": "verified", "ground": "m", "value": "2", "means": "a"},
            {"name": "y", "status": "verified", "ground": "m", "value": "5", "means": "b"},
            {"name": "p", "status": "unverified", "means": "p"}]
    big = {"name": "big", "status": "defined", "ground": "x > 1", "means": "x exceeds 1"}
    both = {"name": "both", "status": "defined", "ground": "big & (y > 4)", "means": "both hold"}
    for named, written in (("big", "x > 1"), ("p = big", "p = (x > 1)"), ("both & p", "((x > 1) & (y > 4)) & p")):
        a = zfl.run({"rows": base + [big, both], "claim": named})
        b = zfl.run({"rows": base, "claim": written})
        assert a["ok"] and b["ok"], (named, a.get("issues"))
        assert a["report"]["numeric"]["disposition"] == b["report"]["numeric"]["disposition"], (named, written)
    loop = [{"name": "u", "status": "defined", "ground": "v & (x > 1)", "means": "m"},
            {"name": "v", "status": "defined", "ground": "u & (y > 1)", "means": "m"}]
    assert any(i["code"] == "E_COMPARE_ROW" for i in zfl.validate({"rows": base + loop, "claim": "u"}))
    mix = [big, {"name": "L", "status": "defined", "ground": "~Tr(L) & big", "means": "m"}]
    assert any(i["code"] == "E_COMPARE_ROW" for i in zfl.validate({"rows": base + mix, "claim": "L"}))
    liar = zfl.run({"rows": [{"name": "L", "status": "defined", "ground": "~Tr(L)", "means": "m"}], "claim": ""})
    assert liar["ok"] and liar["report"]["passport"][0]["kind"] == "PARADOX"
    real = zfl.expand_compares
    zfl.expand_compares = lambda text, rows: (text, False)                     # sabotage
    try:
        assert not zfl.run({"rows": base + [big], "claim": "big & (y > 4)"})["ok"] or \
            zfl.run({"rows": base + [big], "claim": "big & (y > 4)"})["report"]["numeric"]["disposition"] != "EARNED"
    finally:
        zfl.expand_compares = real
    print("   named or written out, one verdict; a loop or a liar leaning on a comparison: E_COMPARE_ROW; sabotage caught")


def sec19_ztl_i_degrees():
    """(2026-11-05) ZTL degrees in the language: a row's degree, the document's threshold and independence. Both sides:
    documents without a degree get no degree section and keep their verdicts; the Fréchet intervals; the three
    threshold outcomes; a told degree that the answer rests on holds the verdict ON CREDIT, one it does not rest on
    does not; independence lands inside; clean and dirty; refusals. Sabotage: dropping the credit cap is caught."""
    print("-" * 72)
    print("§19 ZTL degrees: a row's degree, thresholds, independence")
    A = {"name": "a", "status": "verified", "ground": "m", "degree": "0.3", "means": "a"}
    B = {"name": "b", "status": "verified", "ground": "m", "degree": "0.7", "means": "b"}

    def deg(doc):
        r = zfl.run(doc)
        assert r["ok"], r.get("issues")
        return r["report"].get("degree")
    assert deg({"rows": [dict(A, degree="")], "claim": "a"}) is None
    assert deg({"rows": [A, B], "claim": "a & b"})["interval"] == ["0", "3/10"]
    assert deg({"rows": [A, B], "claim": "a | b"})["interval"] == ["7/10", "1"]
    assert deg({"rows": [A, B], "claim": "a | b", "need": "0.6"})["verdict"] == "EARNED"
    assert deg({"rows": [A, B], "claim": "a & b", "need": "0.5"})["verdict"] == "REFUTED"
    d = deg({"rows": [A, B], "claim": "a & b", "need": "0.2"})
    assert d["verdict"] == "OPEN" and any("independence" in c for c in d["next_check"])
    d = deg({"rows": [A, B], "claim": "a & b", "independent": True, "need": "0.2"})
    assert d["independent"] == ["21/100", "21/100"] and d["verdict"] == "EARNED"
    # a told degree the answer rests on -> ON CREDIT; one it does not rest on -> no cap
    told = dict(A, status="unverified", ground="", degree="0.9")
    d = deg({"rows": [told, dict(B, degree="0.9")], "claim": "a & b", "need": "0.75"})
    assert d["verdict"] == "ON CREDIT" and d["polarity"] == "toward T" and d["rests_on_told"] == ["a"], d
    d = deg({"rows": [dict(A, status="unverified", ground=""), B], "claim": "a | b", "need": "0.6"})
    assert d["verdict"] == "EARNED" and "rests_on_told" not in d, d
    assert deg({"rows": [A], "claim": "a & ~a"})["interval"] == ["0", "0"]
    d = deg({"rows": [{"name": "z", "status": "unverified", "means": "z"}], "claim": "z | ~z", "need": "0.5"})
    assert d["interval"] == ["0", "1"] and d["if_stable"] == ["1", "1"]
    for bad in ({"rows": [dict(A, degree="1.5")], "claim": "a"}, {"rows": [dict(A, status="refuted")], "claim": "a"},
                {"rows": [A], "claim": "a", "need": "2"}):
        assert not zfl.run(bad)["ok"], bad
    real = zfl.degree_report

    def no_cap(doc, rows, claim):                                         # sabotage: the told degree goes uncapped
        out = real(doc, rows, claim)
        if out and out.get("verdict") == "ON CREDIT":
            out["verdict"] = "EARNED" if out.get("polarity") == "toward T" else "REFUTED"
        return out
    zfl.degree_report = no_cap
    try:
        d = deg({"rows": [told, dict(B, degree="0.9")], "claim": "a & b", "need": "0.75"})
        assert d["verdict"] != "ON CREDIT"
    finally:
        zfl.degree_report = real
    print("   no degree -> no section; Fréchet intervals; EARNED / REFUTED / OPEN at a threshold; a told degree")
    print("   that bears -> ON CREDIT, one that does not -> no cap; independence 21/100; refusals; sabotage caught")
    # THE JUDGE READS A DEGREE BY ITS PROJECTION (2026-11-05, the curator: "да, делай Z"): a verified row with a degree
    # strictly inside (0, 1) enters as Z; 1 -> T, 0 -> F; no degree -> its status as before; a told degree stays Z.
    def jd(doc):
        return zfl.run(doc)["report"]["judge"]["disposition"]
    assert jd({"rows": [A, B], "claim": "a & b"}) == "OPEN"                 # was EARNED: probability <= 3/10
    assert jd({"rows": [A, B], "claim": "a | b"}) == "OPEN"
    assert jd({"rows": [dict(A, degree="1"), B], "claim": "a"}) == "EARNED"
    assert jd({"rows": [dict(A, degree="0"), B], "claim": "a"}) == "REFUTED"
    assert jd({"rows": [dict(A, degree="[0.2, 1]"), B], "claim": "a"}) == "OPEN"
    assert jd({"rows": [dict(A, degree=""), B], "claim": "a & b"}) == "OPEN"   # b still 0.7
    assert jd({"rows": [dict(A, degree=""), dict(B, degree="")], "claim": "a & b"}) == "EARNED"
    assert zfl.to_marking([dict(A, status="unverified", ground="", degree="1")]) == {"a": "Z"}
    real_mark = zfl._row_mark
    zfl._row_mark = lambda r: zfl._MARK.get(r.get("status"), "Z")         # sabotage: the status read as truth
    try:
        assert jd({"rows": [A, B], "claim": "a & b"}) == "EARNED"           # the false EARNED comes back
    finally:
        zfl._row_mark = real_mark
    print("   the judge reads a degree by its projection: 0.3 & 0.7 -> OPEN (was a false EARNED), 1 -> T, 0 -> F;")
    print("   no degree -> the status as before; a told degree stays Z; sabotage (status read as truth) caught")
    # CHANCE APART (2026-11-05): a degree row is named as chance, never offered to check; the reverse pass holds it Z
    U = {"name": "c", "status": "unverified", "means": "c"}
    j = zfl.run({"rows": [A, B], "claim": "a & b"})["report"]
    assert j["judge"]["chance"] == ["a", "b"] and "what_to_check" not in j
    assert "verify" not in j["judge"]["why"] and "no check settles it" in j["judge"]["why"], j["judge"]["why"]
    j = zfl.run({"rows": [A, U], "claim": "a | c"})["report"]
    w = j["what_to_check"]
    assert j["judge"]["chance"] == ["a"] and "verify ['c']" in j["judge"]["why"], j["judge"]["why"]
    assert w["EARNED"]["possible"] == [["c"]] and w["REFUTED"]["possible"] == [] and w["REFUTED"]["no_possible_set"], w
    j = zfl.run({"rows": [U, dict(U, name="d")], "claim": "c & d"})["report"]          # the other side: no chance
    assert "chance" not in j["judge"] and j["what_to_check"]["EARNED"]["possible"] == [["c", "d"]]
    real_wtc = zfl.what_to_check
    zfl.what_to_check = lambda claim, m, unv, hold=(): real_wtc(claim, m, unv)       # sabotage: hold ignored
    try:
        assert zfl.run({"rows": [A, U], "claim": "a | c"})["report"]["what_to_check"]["EARNED"]["possible"] != [["c"]]
    finally:
        zfl.what_to_check = real_wtc
    print("   chance apart: named, never offered to check, held Z in the reverse pass; sabotage (hold ignored) caught")
    # PARTIAL INDEPENDENCE (2026-11-06): groups independent of one another, the joint inside a group unknown
    H = [dict(A, name=x, degree="0.5", means=x) for x in ("a", "b", "c")]
    gdoc = {"rows": H, "claim": "a & b & c", "independent": [["a", "b"], ["c"]], "need": "0.2"}
    d = deg(zfl.coerce(gdoc))
    assert d["interval"] == ["0", "1/2"] and d["independent"] == ["0", "1/4"], d          # between Fréchet and 1/8
    assert d["verdict"] == "OPEN" and d["next_check"] == ["the joint inside the group a, b (still unknown)"], d
    assert deg(zfl.coerce(dict(gdoc, independent='[["a", "b"], ["c"]]')))["independent"] == ["0", "1/4"]
    assert deg(zfl.coerce(dict(gdoc, independent=[["a"], ["b"], ["c"]])))["independent"] == ["1/8", "1/8"]
    assert deg(zfl.coerce(dict(gdoc, independent=True)))["independent"] == ["1/8", "1/8"]      # true unchanged
    assert "independent" not in deg(zfl.coerce(dict(gdoc, independent=False)))
    for bad in ([["a"], ["zz"]], [["a", "b"], ["b", "c"]], "maybe", [[]]):
        r = zfl.run(zfl.coerce(dict(gdoc, independent=bad)))
        assert not r["ok"] and any(i["code"] == "E_INDEPENDENT" for i in r["issues"]), (bad, r.get("issues"))
    assert "in no group" in deg(zfl.coerce(dict(gdoc, independent=[["a"], ["b"]])))["refused"]
    real_g = zfl.zdegree.degree_groups
    zfl.zdegree.degree_groups = lambda f, dg, groups, **k: zfl.zdegree.degree_independent(f, dg)  # sabotage: groups ignored
    try:
        assert deg(zfl.coerce(gdoc))["independent"] != ["0", "1/4"]
    finally:
        zfl.zdegree.degree_groups = real_g
    print("   partial independence: groups [a, b] | [c] give a & b & c in [0, 1/4] (Fréchet [0, 1/2], all independent")
    print("   1/8); JSON text accepted; true unchanged; bad groups E_INDEPENDENT; an atom in no group refused; sabotage")
    # A SEARCH THAT FOUND NOTHING PROVES NO "NONE" (2026-11-06; Pell 61: no root with 1 <= y <= 10^6, and one exists)
    S = lambda kind: {"name": "no_root", "status": "verified", "ground": "search_y_le_1e6", "ground_kind": kind,
                      "means": "x^2 - 61 y^2 = 1 has no root"}
    r = zfl.run(zfl.coerce({"rows": [S("search")], "claim": "no_root"}))
    j = r["report"]["judge"]
    assert r["ok"] and j["disposition"] == "OPEN" and j["search_not_proof"] == ["no_root"], j
    assert "chance" not in j and r["report"]["what_to_check"]["EARNED"]["possible"] == [["no_root"]]
    assert any(i["code"] == "W_SEARCH_NOT_PROOF" for i in r["issues"])
    r = zfl.run(zfl.coerce({"rows": [S("document")], "claim": "no_root"}))                 # the other side
    assert r["report"]["judge"]["disposition"] == "EARNED" and "search_not_proof" not in r["report"]["judge"]
    assert not any(i["code"] == "W_SEARCH_NOT_PROOF" for i in r["issues"])
    r = zfl.run(zfl.coerce({"rows": [dict(S("search"), status="unverified", ground="")], "claim": "no_root"}))
    assert not any(i["code"] == "W_SEARCH_NOT_PROOF" for i in r["issues"])                  # only verified rows
    real_m = zfl._row_mark
    zfl._row_mark = lambda row: zfl._MARK.get(row.get("status"), "Z")                   # sabotage: search read as proof
    try:
        assert zfl.run(zfl.coerce({"rows": [S("search")], "claim": "no_root"}))["report"]["judge"]["disposition"] == "EARNED"
    finally:
        zfl._row_mark = real_m
    print("   a search that found nothing: the row is read as not verified (OPEN, W_SEARCH_NOT_PROOF, offered to")
    print("   prove); the same row on a document EARNED; sabotage (search read as proof) caught")
    # CLASSICAL REASONING IS SAFE only where every statement read is clean (2026-11-06, ZAxiomsRead)
    C = lambda n, **k: dict({"name": n, "status": "verified", "ground": "m", "means": n}, **k)
    cs = lambda rows, claim: zfl.run(zfl.coerce({"rows": rows, "claim": claim}))["report"]["judge"].get("classical_safe")
    assert cs([C("a"), C("b", status="refuted")], "a | b") is True
    assert cs([C("a"), {"name": "c", "status": "unverified", "means": "c"}], "a & c") is None    # a dirty input
    assert cs([C("a", degree="0.5")], "a") is None and cs([C("a", ground_kind="search")], "a") is None
    print("   classical_safe: set when every statement read is T or F; not with a dirty, chance or searched input")
    try:
        import backread
    except ImportError:                                                     # the mirror lives in the studio only
        return
    # THE MIRROR'S CLAIM NOTE, NARROWED (2026-11-05): not for numeric or degree claims; the original a ^ b case stays
    assert backread.факты({"rows": [U, dict(U, name="d")], "claim": "c ^ d"})["claim_bypassed_passport"] is True
    assert backread.факты({"rows": [A, B], "claim": "a & b"})["claim_bypassed_passport"] is False
    import zflexamples as X
    hits = {}
    for e in X.EXAMPLES:
        if backread.факты(e["doc"])["claim_bypassed_passport"]:
            hits[e.get("kind")] = hits.get(e.get("kind"), 0) + 1
    assert not hits.get("numbers") and not hits.get("audit") and not hits.get("paradox"), hits
    print(f"   the mirror's claim note: a ^ b on unverified rows yes, degrees no; over the catalogue {hits}")


def sec20_a_system_of_equations_is_a_question_too():
    """(2026-11-08, the curator's "Синтаксис систем в ZFL — принято. Делай."; answer A first) Several unknowns `x=?`
    and a claim made of as many equations is a SYSTEM: zsystem proves a solution in a cube, the only one there
    (Krawczyk, the contraction form, checked exactly with the kernel's readings); the answer says that solutions
    outside the cube are not excluded (W_SYSTEM_LOCAL). Both sides: a nonlinear system is solved (and the solution
    satisfies the equations, checked in floats, a route the kernel does not take); a parameter on credit makes the
    answer ON CREDIT; a system with no real solution is not "solved"; a claim with an inequality is not a system;
    a linear system keeps the exact solver. Forgeries of the certificate are refused."""
    import math
    import zsystem
    from fractions import Fraction
    print("-" * 72)
    print("§20 a system of equations is a question too")
    U = lambda n: {"name": n, "means": n, "status": "unverified", "value": "?"}
    r = zfl.run({"rows": [U("x"), U("y")], "claim": "x*x + y*y = 1 & x = exp(y)"})
    n = r["report"]["numeric"]
    assert r["ok"] and n["disposition"] == "EARNED" and n["verdict"] == "T", n
    assert any(i["code"] == "W_SYSTEM_LOCAL" for i in r["issues"]), r["issues"]
    x = float(Fraction(n["solved"]["x"]["lo"]) + Fraction(n["solved"]["x"]["hi"])) / 2
    y = float(Fraction(n["solved"]["y"]["lo"]) + Fraction(n["solved"]["y"]["hi"])) / 2
    assert abs(x * x + y * y - 1) < 1e-5 and abs(x - math.exp(y)) < 1e-5, (x, y)
    print(f"   x*x + y*y = 1 & x = exp(y): EARNED, a solution near ({x:.6f}, {y:.6f}), unique in its cube")
    rows = [U("x"), U("y"), U("z"), {"name": "a", "means": "a", "status": "unverified", "value": "[1.99,2.01]"},
            {"name": "b", "means": "b", "status": "unverified", "value": "[0.49,0.51]"}]
    r = zfl.run({"rows": rows, "claim": "x + y + z = 3 & x*exp(y) = a & ln(z) + x*y = b"})
    n = r["report"]["numeric"]
    assert n["disposition"] == "ON CREDIT" and n["verdict"] == "T" and set(n["solved"]) == {"x", "y", "z"}, n
    print("   3×3 with parameters on credit: ON CREDIT, a solution for every parameter in the box")
    r = zfl.run({"rows": [U("x"), U("y")], "claim": "x*x + y*y = -1 & x = y"})
    assert not r["report"]["numeric"]["solved"] and r["report"]["numeric"]["verdict"] != "T"
    assert not any(i["code"] == "W_SYSTEM_LOCAL" for i in r["issues"])
    r = zfl.run({"rows": [U("x"), U("y")], "claim": "x*x + y*y <= 1 & x = exp(y)"})
    assert not any(i["code"] == "W_SYSTEM_LOCAL" for i in r["issues"])
    r = zfl.run({"rows": [U("x"), U("y")], "claim": "x + y = 3 & x - y = 1"})
    n = r["report"]["numeric"]
    assert n["solved"]["x"]["pinned"] and n["solved"]["x"]["lo"] == "2", n
    r = zfl.run({"rows": [U("s"), U("area")], "claim": "area == s*s & area - 5*s + 6 == 0"})
    n = r["report"]["numeric"]
    assert n["solved"]["s"].get("roots") == ["2", "3"] and not n["solved"]["s"].get("system"), n
    print("   no real solution: not solved; an inequality: not a system; a linear system and paired exact roots:")
    print("   the exact solver's answer stays (it is complete; the system's is local)")
    # forgeries of the certificate
    import znumjudge as ZJ
    qs = ZJ.parse_quantities("x=? credit, y=? credit")[0]
    laws = [ZJ._parse_arith("(x*x + y*y) - (1)", qs), ZJ._parse_arith("(x) - (exp(y))", qs)]
    cert, res = zsystem.search(laws, ["x", "y"], qs)
    assert res[0]
    far = dict(cert, centre=[str(Fraction(c) + Fraction(1, 64)) for c in cert["centre"]])
    assert not zsystem.check(laws, ["x", "y"], qs, far)[0]
    wide = dict(cert, radius="1")
    assert not zsystem.check(laws, ["x", "y"], qs, wide)[0]
    flat = dict(cert, Z=[["0", "0"], ["0", "0"]])
    assert not zsystem.check(laws, ["x", "y"], qs, flat)[0]
    print("   forged certificates refused: the cube moved off the solution, a radius 1 (no contraction), Z = 0")


def sec21_a_system_in_a_search_region_is_answered_completely():
    """(2026-11-08, the curator's "Делай Б") Every unknown with a search region `x = ? in [a, b]`: the region is
    exhausted (each box excluded by the kernel's readings or inside a certified solution's cube) and the answer is
    COMPLETE (W_SYSTEM_ALL). Both sides: the circle meets the exponential twice in [-2, 2]² — both found, each checked
    against the equations in floats; x² + y² = −1 has none — REFUTED; without regions the answer stays local
    (W_SYSTEM_LOCAL); a region on a single unknown is said to be unused (W_REGION_UNUSED); a malformed region is
    an error at the cell (E_VALUE_FORM). Sabotage: with the exclusion switched off the region is never exhausted —
    no complete answer is claimed."""
    import math
    import zsystem
    from fractions import Fraction
    print("-" * 72)
    print("§21 a system in a search region is answered completely")
    U = lambda n, v="?": {"name": n, "means": n, "status": "unverified", "value": v}
    r = zfl.run({"rows": [U("x", "? in [-2, 2]"), U("y", "? in [-2, 2]")], "claim": "x*x + y*y = 1 & x = exp(y)"})
    n = r["report"]["numeric"]
    assert n["disposition"] == "EARNED" and n["system"]["complete"] and n["system"]["solutions"] == 2, n
    assert any(i["code"] == "W_SYSTEM_ALL" for i in r["issues"])
    pts = []
    for bx, by in zip(n["solved"]["x"]["roots"], n["solved"]["y"]["roots"]):
        x = float(sum(Fraction(t) for t in bx.strip("[]").split(","))) / 2
        y = float(sum(Fraction(t) for t in by.strip("[]").split(","))) / 2
        assert abs(x * x + y * y - 1) < 1e-5 and abs(x - math.exp(y)) < 1e-5, (x, y)
        pts.append((round(x, 6), round(y, 6)))
    print(f"   the circle meets the exponential in [-2,2]²: ALL the solutions, {sorted(pts)}")
    r = zfl.run({"rows": [U("x", "? in [-2, 2]"), U("y", "? in [-2, 2]")], "claim": "x*x + y*y = -1 & x = y"})
    assert r["report"]["numeric"]["disposition"] == "REFUTED" and r["report"]["numeric"]["verdict"] == "F"
    r = zfl.run({"rows": [U("x"), U("y")], "claim": "x*x + y*y = 1 & x = exp(y)"})
    assert any(i["code"] == "W_SYSTEM_LOCAL" for i in r["issues"]) and not r["report"]["numeric"]["system"]["complete"]
    r = zfl.run({"rows": [U("x", "? in [0, 10]")], "claim": "x*x = 2"})
    assert any(i["code"] == "W_REGION_UNUSED" for i in r["issues"])
    r = zfl.run({"rows": [U("x", "? in [a, b]")], "claim": "x*x = 2"})
    assert not r["ok"] and any(i["code"] == "E_VALUE_FORM" for i in r["issues"])
    print("   none in the region: REFUTED; no regions: local; one unknown with an exact answer: unused, said; "
          "a malformed region: refused")
    import znumjudge as ZJ
    qs = ZJ.parse_quantities("x=? credit, y=? credit")[0]
    laws = [ZJ._parse_arith("(x*x + y*y) - (1)", qs), ZJ._parse_arith("(x) - (exp(y))", qs)]
    keep = zsystem._excluded
    zsystem._excluded = lambda laws, qs, box: False
    try:
        res = zsystem.solve_all(laws, ["x", "y"], qs, {"x": (Fraction(-2), Fraction(2)), "y": (Fraction(-2), Fraction(2))},
                                budget=400)
    finally:
        zsystem._excluded = keep
    assert not res["complete"], res
    print("   sabotage: with the exclusion off the region is never exhausted — no complete answer")


if __name__ == "__main__":
    print("=" * 72)
    print("ZFL v2 — the table, headless")
    print("=" * 72)
    sec1_one_table_three_instruments()
    sec2_the_cells_are_checked_where_the_eye_is()
    sec3_the_ledger_appears_when_it_is_wanted()
    sec3b_what_the_ground_column_is_actually_for()
    sec4_an_unknown_is_a_question_not_a_gap()
    sec7_the_ground_gate_demotes_phantom_words()
    sec8_the_credit_that_cannot_be_redeemed()
    sec9_the_world_has_a_clock_too()
    sec10_what_the_ground_holds_and_what_to_check()
    sec11_a_public_service_cannot_be_made_to_raise_or_to_stall()
    sec13_naive_sets_are_in_the_language()
    sec15_a_convention_changes_the_order_never_the_verdict()
    sec16_a_lone_equals_is_read_by_the_types_of_its_sides()
    sec17_a_clock_beside_a_numeric_claim_never_crashes()
    sec18_a_comparison_can_be_named()
    sec19_ztl_i_degrees()
    sec20_a_system_of_equations_is_a_question_too()
    sec21_a_system_in_a_search_region_is_answered_completely()
    sec22_a_system_with_sin_cos_tan_in_a_search_region()
    sec23_one_unknown_in_a_search_region()
    sec4b_every_example_runs_and_json_types_are_taken_as_they_come()
    sec5_the_spec_can_build_the_form_and_the_page()
    print("=" * 72)
    print("ZFL FOUNDATION GREEN — one table, the genre computed rather than declared,")
    print("errors addressed to the cell the eye is on, and the numeric floor,")
    print("the passport office and the ledger all reachable without choosing")
    print("a tab or learning a syntax. The form and the reference page are")
    print("views over the same spec the validator enforces.")
