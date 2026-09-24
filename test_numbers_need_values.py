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
And a refusal says what it refused: a comparison nested in a comparison is
a ValueError in words, not "'NoneType' object has no attribute 'group'".
And a number is not a statement: `x^2` (XOR) or `m & p` over a number is
E_NUMBER_AS_STATEMENT, where it used to be read silently and answered OPEN.
Fails on the validator and on the splitter before the change.
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

# 5. a refusal says what it refused: a side that is not arithmetic
#    (MEASURED 2026-09-24: a live model wrote `eq0 == (x*x - 2*x + 5 == 0)`;
#    the splitter died as AttributeError, "'NoneType' object has no attribute
#    'group'", and that sentence was all the person and the repair loop got)
import znumjudge
for claim in ("eq0 == (x*x - 2*x + 5 == 0) & exists == eq0", "(p & x) == 3"):
    try:
        znumjudge.extract_comparisons(claim, dict.fromkeys(["x", "eq0", "exists", "p"]))
        said = "no refusal"
    except ValueError as exc:
        said = str(exc)
    except Exception as exc:
        said = f"{type(exc).__name__}: {exc}"
    check("not arithmetic" in said, f"{claim!r}: the splitter refuses in words, got {said!r}")
doc = {"rows": [unverified("x", value="?"), unverified("eq0"), unverified("exists")],
       "claim": "eq0 == (x*x - 2*x + 5 == 0) & exists == eq0"}
hints = [i["hint"] for i in zfl.run(doc)["issues"] if i["level"] == "error"]
check(hints and "not arithmetic" in hints[0] and "NoneType" not in hints[0],
      f"the run's refusal is in words: {hints}")

# 6. a number is not a statement (MEASURED 2026-09-24: a live model wrote
#    `x^2 - 2*x + 5 == 0`, `^` being XOR, read silently as "x XOR (...)", OPEN)
for rows, claim in [([unverified("x", value="?"), unverified("eq")], "x^2 - 2*x + 5 == 0"),
                    ([verified("x", value="2")], "x^2 == 4"),
                    ([verified("m", value="5"), unverified("p")], "m & p"),
                    ([unverified("rain"), verified("budget", value="5000")], "rain -> budget")]:
    doc = {"rows": rows, "claim": claim}
    check(errors(doc) == [("E_NUMBER_AS_STATEMENT", "claim")], f"{claim!r}: {errors(doc)}")
    check(set(run_errors(doc)) == {"E_NUMBER_AS_STATEMENT"}, f"{claim!r}: the run stops on it")
hint = [i["hint"] for i in zfl.validate({"rows": [verified("x", value="2")], "claim": "x^2 == 4"})
        if i["code"] == "E_NUMBER_AS_STATEMENT"][0]
check("x*x" in hint and "XOR" in hint, f"the hint names the cure: {hint!r}")
for rows, claim in [([verified("x", value="2")], "x*x == 4"),
                    ([verified("m", value="[0,9]"), unverified("p")], "(m == m) & p"),
                    ([unverified("p"), verified("q")], "p ^ q"),
                    ([verified("m", value="[0,9]"), unverified("p")], "(m > 3) -> p")]:
    doc = {"rows": rows, "claim": claim}
    check(errors(doc) == [], f"{claim!r}: validate {errors(doc)} on a claim that was fine")

# 4. no catalogue example is touched, in any language
langs = ("en", "ru", "uk", "he", "de", "fr", "es")
n = 0
for lang in langs:
    for item in zflexamples.catalogue(lang)["items"]:
        n += 1
        codes = [i["code"] for i in zfl.validate(item["doc"])]
        check("E_NO_VALUE" not in codes and "E_NUMBER_AS_STATEMENT" not in codes,
              f"catalogue [{lang}] {item.get('label')!r}: {codes}")
check(n == 46 * len(langs), f"the catalogue was read: {n} documents")

print(f"NUMBERS NEED VALUES GREEN — {CHECKS} checks; {n} catalogue documents untouched")
