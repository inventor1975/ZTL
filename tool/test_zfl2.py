# -*- coding: utf-8 -*-
"""
ZFL v2 end to end, with no browser in the way.

The studio is the point of this work, but a language that can only be
exercised through a web page is a language nobody can test. Everything the
form will do — validate a cell, assemble the sheet, decide which
instruments apply, run them — happens here first, headless and under
assert, so the UI can be a view over something already known to work rather
than the only place it works at all.

Run:  python3 tool/test_zfl2.py
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import zfl2                                                      # noqa: E402

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
    r = zfl2.run(MIXED)
    assert r["ok"], r["issues"]
    print(f"   applies: {r['applies']}")
    assert r["applies"] == {"numeric": True, "passport": True,
                            "ledger": True, "judge": True}
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
    issues = zfl2.validate(bad)
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
    r = zfl2.run(doc)
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
    ia = zfl2.run(apart)["report"]["ledger"]["brackets"]
    isame = zfl2.run(same)["report"]["ledger"]["brackets"]
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
        r = zfl2.run(doc)
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
    import zfl2examples as X
    kinds = {}
    for e in X.EXAMPLES:
        r = zfl2.run(e["doc"])
        assert r["ok"], (e["en"], r["issues"])
        kinds.setdefault(e["kind"], 0)
        kinds[e["kind"]] += 1
    print(f"   {len(X.EXAMPLES)} examples, all validating and running: {kinds}")
    # THE PUBLISHED PROMISE. §7 of the paradox docket (v1.1, DOI
    # 10.5281/zenodo.21916017) tells the reader the studio holds this
    # paper's entire collection and names the cases. A studio missing one
    # of them does not have a gap — it makes an issued paper false. So the
    # list is checked here, by the names the v1 studio used, which are the
    # names the paper quotes.
    import ztlstudio
    promised = {e["name"] for e in ztlstudio.EXAMPLES}
    present = {e.get("paper") for e in X.EXAMPLES if e.get("paper")}
    print(f"   cases the docket promises: {len(promised)}, present: "
          f"{len(present & promised)}")
    assert promised <= present, sorted(promised - present)
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
    r = zfl2.run(doc)
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
        spec = zfl2.form_spec(lang)
        cols = spec["columns"]
        assert len(cols) == len(zfl2.COLUMNS)
        assert all(c["label"] and c["help"] for c in cols)
        widgets = sorted({c["widget"] for c in cols})
        print(f"   {lang}: {len(cols)} columns, widgets {widgets}")
        for c in cols:
            if c["widget"] in ("choice", "multi"):
                assert c["options"] and all(o["label"] for o in c["options"])
    req = [c["key"] for c in zfl2.form_spec()["columns"] if c["required"]]
    cond = [c["key"] for c in zfl2.form_spec()["columns"]
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
    a = zfl2.run(doc)
    ja = a["report"]["judge"]
    assert (ja["verdict"], ja["grade"]) == ("T", "hereditary")
    assert "demoted_grounds" not in a["report"]          # без реестра — как раньше
    b = zfl2.run(doc, ground_registry={"inv-17"})
    jb = b["report"]["judge"]
    assert jb["verdict"] == "F" and jb["disposition"] == "OPEN"
    assert b["report"]["demoted_grounds"] == ["p"]       # поимённо
    c = zfl2.run({"rows": [doc["rows"][1]], "claim": "q"},
                 ground_registry={"inv-17"})
    jc = c["report"]["judge"]
    assert (jc["verdict"], jc["grade"]) == ("T", "hereditary")
    print("   without a registry: byte-identical behaviour;")
    print("   with one: the phantom is demoted BY NAME and the verdict")
    print("   honestly falls OPEN; a registered ground still earns.")

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
    sec4b_every_example_runs_and_json_types_are_taken_as_they_come()
    sec5_the_spec_can_build_the_form_and_the_page()
    print("=" * 72)
    print("ZFL2 GREEN — one table, the genre computed rather than declared,")
    print("errors addressed to the cell the eye is on, and the numeric floor,")
    print("the passport office and the ledger all reachable without choosing")
    print("a tab or learning a syntax. The form and the reference page are")
    print("views over the same spec the validator enforces.")
