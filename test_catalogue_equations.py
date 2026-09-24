# -*- coding: utf-8 -*-
"""
test_catalogue_equations — the catalogue shows what the studio solves.

Until 2026-09-24 the studio solved equations (a quadratic by its reading,
exact roots such as √2, a cubic by Sturm) and the catalogue a visitor
clicks showed none of it: five number examples, all linear or a box. Five
equations were added, each asked in seven languages as a person asks it,
and each verdict is pinned here, because an example is a promise about the
machine:

  x*x - 2*x + 5 == 0              REFUTED — no real x, not "no answer"
  x*x - 5*x + 6 == 0              x = 2 or 3 — two worlds, not the box [2, 3]
  x*x == 2                        x = -√2 or √2 — exact, not a decimal
  the square plot                 REFUTED — the first equation told as a story
  x*x*x - 6*x*x + 11*x - 6 == 0   x = 1, 2 or 3

MEASURED 2026-09-24 before writing the examples: with units on the plot
(side in m, area in m2) the claim is refused, "cannot add 'm2' with 'm'",
because area - 2*s + 5 adds square metres to metres. The example leaves the
units out on purpose, and the refusal is pinned too, so the comment that
says so in zflexamples.py cannot go stale. So are the limits the HF Space's
README states (real numbers only, degree 8, exact only when rational or a
quadratic's p + q√d, otherwise ≈ and OPEN).
Fails before the change: the five labels are not in the catalogue.
Run: python3 test_catalogue_equations.py  ->  CATALOGUE EQUATIONS GREEN
"""
import json

import zfl
import zflexamples

CHECKS = 0


def check(cond, what):
    global CHECKS
    CHECKS += 1
    if not cond:
        raise SystemExit(f"FAIL: {what}")
    print(f"  ok  {what}")


def numeric(doc):
    r = zfl.run(doc)
    return r, (r.get("report") or {}).get("numeric") or {}


BY_LABEL = {e["en"]: e for e in zflexamples.EXAMPLES}
EXPECT = [
    ("a quadratic with no real root", "x*x - 2*x + 5 == 0", "REFUTED", None),
    ("a quadratic with two roots", "x*x - 5*x + 6 == 0", "EARNED", {"x": ["2", "3"]}),
    ("the root of 2, exact and not a decimal", "x*x == 2", "EARNED", {"x": ["-√2", "√2"]}),
    ("a square plot that cannot exist", "(area == s*s) & (area - 2*s + 5 == 0)", "REFUTED", None),
    ("a cubic with three roots", "x*x*x - 6*x*x + 11*x - 6 == 0", "EARNED", {"x": ["1", "2", "3"]}),
]

# 1. each example is in the catalogue, runs, and says what it promises
print("1. the five equations and their verdicts")
for label, claim, disposition, roots in EXPECT:
    e = BY_LABEL.get(label)
    check(e is not None and e["kind"] == "numbers", f"{label!r} is a numbers example")
    check(e["doc"]["claim"] == claim, f"{label!r}: the claim is {claim!r}")
    r, n = numeric(e["doc"])
    check(r["ok"] and not r["issues"], f"{label!r}: validates and runs, no issues")
    check(n.get("disposition") == disposition, f"{label!r}: {n.get('disposition')} (want {disposition})")
    solved = n.get("solved") or {}
    if roots is None:
        check(solved == {}, f"{label!r}: nothing is solved, because nothing can be")
    else:
        got = {k: v.get("roots") for k, v in solved.items()}
        check(got == roots, f"{label!r}: roots {got}")
        for k in roots:
            check(solved[k]["prov"] == "earned", f"{label!r}: {k} is earned, not on credit")

# 2. the two roots are two worlds: 2.5 lies in the box and is not a root
_, n = numeric(BY_LABEL["a quadratic with two roots"]["doc"])
x = n["solved"]["x"]
check((x["lo"], x["hi"]) == ("2", "3") and x["roots"] == [x["lo"], x["hi"]],
      "the hull [2, 3] is reported, and the answer is its two ends, not its inside")

# 3. seven languages: every label and every question is there, and the
# document a German reader runs is the document the English reader runs
print("2. seven languages")
langs = ("en", "ru", "uk", "he", "de", "fr", "es")
for label, *_ in EXPECT:
    e = BY_LABEL[label]
    for lang in langs:
        check(bool(e.get(lang)) and bool(e.get(f"ask_{lang}")), f"{label!r} [{lang}]: label and question")
    reports = set()
    for lang in langs:
        item = next(i for i in zflexamples.catalogue(lang)["items"] if i["label"] == e[lang])
        reports.add(json.dumps(zfl.run(item["doc"]).get("report"), sort_keys=True, default=str))
    check(len(reports) == 1, f"{label!r}: one report in all seven languages")

# 4. the units the plot leaves out, and why
print("3. the plot with units is refused, as the comment says")
plot = BY_LABEL["a square plot that cannot exist"]["doc"]
rows = [dict(plot["rows"][0], unit="m"), dict(plot["rows"][1], unit="m2")]
r = zfl.run(dict(plot, rows=rows))
codes = [(i["code"], i.get("hint", "")) for i in r["issues"]]
check(not r["ok"] and any(c == "E_UNREADABLE" and "cannot add 'm2' with 'm'" in h for c, h in codes),
      f"side in m, area in m2: refused, {codes[:1]}")


# 5. the limits the Space's README states (ztl-space/hf/README.md, "It
# solves, too"), each as the page shows it, so the public text cannot drift
print("4. the limits the README states")
X = {"name": "x", "means": "the unknown", "status": "unverified", "value": "?"}
for claim, disposition, roots in [
        ("x*x + 1 == 0", "REFUTED", None),
        ("x*x - 2*x - 1 == 0", "EARNED", ["1-√2", "1+√2"]),
        ("x*x*x == 2", "OPEN", ["≈1.25992104989"]),
        ("x*x*x*x - 5*x*x + 6 == 0", "OPEN",
         ["≈-1.73205080757", "≈-1.41421356237", "≈1.41421356237", "≈1.73205080757"]),
        ("x*x*x*x*x*x*x*x*x - 2 == 0", "OPEN", None)]:
    r, n = numeric({"rows": [X], "claim": claim})
    got = (n.get("solved") or {}).get("x", {}).get("roots")
    check(r["ok"] and n.get("disposition") == disposition and got == roots,
          f"{claim!r}: {n.get('disposition')}, roots {got}")

print(f"CATALOGUE EQUATIONS GREEN — {CHECKS} checks")
