# -*- coding: utf-8 -*-
"""
test_numbers_need_values — a name READ AS A NUMBER must have a value.

Inside a comparison every name is a quantity. A row with no value is not a
quantity, so no instrument can read such a claim. Until 2026-09-24 the
validator let every comparison through (`_formula` hands it to the sheet
judge) and the run refused it afterwards.

MEASURED 2026-09-24 on the live studio, three questions in prose (two
Russian, one English), e.g. "is there a number x such that x squared minus
2x plus 5 equals zero?": the translator wrote the right formula every time,
`x*x - 2*x + 5 == 0`, and every time it left the sought x without a value
instead of `?`. `validate` returned nothing, so the repair loop, which runs
on the validator's issues, never ran, and the person saw E_UNREADABLE
"stray character '*'". With a lone `=` and no values in the table the same
claim died in the propositional parser as E_CLAIM, "stray character '*'".

Guards: the issue is E_NO_VALUE, addressed to the row's value cell, with the
cure (`?`) in its hint, for `==`, for a lone `=`, for an order comparison,
for a system of two relations, and when only some rows have values; the run
stops on it instead of E_UNREADABLE. Untouched: purely logical claims (->,
=, <->), mixed claims whose logical atoms have no value, a genuine syntax
error (still E_CLAIM), and every catalogue example in seven languages.
Fails on the validator before the change.
Run: python3 test_numbers_need_values.py  ->  NUMBERS NEED VALUES GREEN
"""
import sys

import zfl
import zflexamples

CHECKS = 0


def check(cond, what):
    global CHECKS
    CHECKS += 1
    if not cond:
        print("FAIL:", what)
        sys.exit(1)


def unverified(name, **kw):
    return dict({"name": name, "means": "a quantity", "status": "unverified"}, **kw)


def verified(name, **kw):
    return dict({"name": name, "means": "a quantity", "status": "verified",
                 "ground": "doc-1"}, **kw)


def errors(doc):
    return sorted((i["code"], i["where"]) for i in zfl.validate(doc)
                  if i["level"] == "error")


def run_errors(doc):
    return sorted(i["code"] for i in zfl.run(doc).get("issues", [])
                  if i["level"] == "error")


# 1. the measured case and its siblings: the cell and the cure
NEEDS = [
    ([unverified("x")], "x*x - 2*x + 5 == 0", [("E_NO_VALUE", "row 1 / value")]),
    ([unverified("x")], "x*x - 2*x + 5 = 0", [("E_NO_VALUE", "row 1 / value")]),
    ([unverified("x")], "x > 0", [("E_NO_VALUE", "row 1 / value")]),
    ([unverified("s", ground="the-story"), unverified("area", ground="the-story")],
     "(area == s*s) & (area - 2*s + 5 == 0)",
     [("E_NO_VALUE", "row 1 / value"), ("E_NO_VALUE", "row 2 / value")]),
    ([verified("y", value="5"), unverified("x")], "x*x == y", [("E_NO_VALUE", "row 2 / value")]),
]
for rows, claim, want in NEEDS:
    doc = {"rows": rows, "claim": claim}
    check(errors(doc) == want, f"{claim!r}: validate {errors(doc)} != {want}")
    got = run_errors(doc)
    check(got and set(got) == {"E_NO_VALUE"}, f"{claim!r}: run stops on {got}, not on E_NO_VALUE")
hint = [i["hint"] for i in zfl.validate({"rows": [unverified("x")], "claim": "x*x - 2*x + 5 == 0"})
        if i["code"] == "E_NO_VALUE"][0]
check("'x'" in hint and "?" in hint, f"the hint names the row and the cure: {hint!r}")

# 2. the cure works: with `?` the claim is a question and the numeric floor answers
for claim in ("x*x - 2*x + 5 == 0", "x*x - 2*x + 5 = 0", "2*x + 3 = 7"):
    doc = {"rows": [unverified("x", value="?")], "claim": claim}
    check(errors(doc) == [], f"{claim!r} with x = ?: validate {errors(doc)}")
    r = zfl.run(doc)
    check(r["ok"] and (r["report"].get("numeric") or {}).get("disposition"),
          f"{claim!r} with x = ?: the numeric floor answers ({r.get('issues')})")

# 3. untouched: logic, mixed claims, a real syntax error
QUIET = [
    ([unverified("p"), verified("q")], "p -> q"),
    ([unverified("p"), verified("q")], "p = q"),
    ([unverified("p"), verified("q")], "p <-> q"),
    ([verified("m", value="[0,9]"), unverified("p")], "(m == m) & p"),
    ([verified("m", value="[0,9]"), unverified("p")], "(m > 3) -> p"),
]
for rows, claim in QUIET:
    doc = {"rows": rows, "claim": claim}
    check(errors(doc) == [], f"{claim!r}: validate {errors(doc)} on a claim that was fine")
    check(zfl.run(doc)["ok"], f"{claim!r}: the run stopped on a claim that was fine")
doc = {"rows": [unverified("p"), verified("q")], "claim": "p & & q"}
check(errors(doc) == [("E_CLAIM", "claim")], f"a real syntax error stays E_CLAIM: {errors(doc)}")

# 4. no catalogue example is touched, in any language
langs = ("en", "ru", "uk", "he", "de", "fr", "es")
n = 0
for lang in langs:
    for item in zflexamples.catalogue(lang)["items"]:
        n += 1
        codes = [i["code"] for i in zfl.validate(item["doc"])]
        check("E_NO_VALUE" not in codes, f"catalogue [{lang}] {item.get('label')!r}: {codes}")
check(n == 41 * len(langs), f"the catalogue was read: {n} documents")

print(f"NUMBERS NEED VALUES GREEN — {CHECKS} checks; {n} catalogue documents untouched")
