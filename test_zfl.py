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
                            "ledger": True, "epoch": False, "judge": True}
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
    appear on an ordinary unverified atom, and the verdict itself is
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

    # An ordinary unverified atom is a real credit — it must NOT be marked.
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
    came out, and — for a claim still resting on unverified inputs — which
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
    assert "refused" in w and "up to 6" in w["refused"], w
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
    near = "*".join(["a"] * 2040) + " > b"            # just under the cap
    t0 = time.time()
    r = zfl.run({"claim": near, "rows": rows})
    assert "E_TOOLONG" not in [i["code"] for i in r.get("issues", [])] and time.time() - t0 < 2.0, r
    print("   a value past float range is an issue, not a traceback; a formula")
    print("   over 4096 characters is refused by name; one under it reads fast.")


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
    sec4b_every_example_runs_and_json_types_are_taken_as_they_come()
    sec5_the_spec_can_build_the_form_and_the_page()
    print("=" * 72)
    print("ZFL FOUNDATION GREEN — one table, the genre computed rather than declared,")
    print("errors addressed to the cell the eye is on, and the numeric floor,")
    print("the passport office and the ledger all reachable without choosing")
    print("a tab or learning a syntax. The form and the reference page are")
    print("views over the same spec the validator enforces.")
