# -*- coding: utf-8 -*-
"""WHICH ROOT IS AN ANSWER (znumsolve.solve_claim, 2026-11-27). The curator, on (x*x == 4) & ((x > 0) | p) with p dirty:
«при −2, это (T) ∧ (F ∨ p) — отсюда (T) ∧ (F) — и получаем F»; «при 2 … (T) ∧ (T) — и получаем T».

The rule checked here: a root is an answer where the claim's VALUE is T under it; the disposition is the weakest of
the answers'; a root whose value is F and that is not refuted is not an answer and is not lost (`roots_standing`,
in ZFL `roots_left`). When no root holds now, the disposition speaks of the roots not refuted.

THE DEFECT THIS REPLACES (MEASURED 2026-11-27, kernel 8417ec8): (x*x == 4) & ((x > 0) | (p & ~p)) came back REFUTED IF
STABLE - the verdict of the root -2 given to the whole claim, although x = 2 earns it read by read.

Both sides: claims with no dirty ground keep their answers; a refuted root goes as before; roots on credit stay
answers on credit; a quantity that depends on the unknown follows the answer kept. Sabotage: the value of a root
not read (the old "every root not refuted is kept") - the open root weighs on the earned one again.
Run: python3 test_root_answers.py"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import znumsolve                                              # noqa: E402
from znumjudge import parse_quantities                        # noqa: E402
import zfl                                                    # noqa: E402

CHECKS, FAILS = 0, []


def check(c, what, show=None):
    global CHECKS
    CHECKS += 1
    if not c:
        FAILS.append(what)
        print("FAIL:", what, "" if show is None else show)


def solve(claim, sheet="x=? credit"):
    q, m = parse_quantities(sheet)
    r = znumsolve.solve_claim(claim, q, dict(m, p="Z"))
    x = r["solved"].get("x")
    return (r["disposition"], (str(x["lo"]), str(x["hi"])) if x else None,
            {t["root"]: (t["disposition"], t["answer"]) for t in (r.get("roots_standing") or {}).get("x", [])}, r)


NOW, NO = "now", "no"
BOTH = ("-2", "2")
# claim -> disposition, the answer kept for x, and per root: (its disposition, how its `answer` starts)
CASES = [
    # the two the curator worked by hand, and the defect
    ("(x*x == 4) & ((x > 0) | p)", "EARNED", ("2", "2"), {"-2": ("OPEN", "not settled: it turns on verify p"), "2": ("EARNED", NOW)}),
    ("(x*x == 4) & ((x > 0) | (p & ~p))", "EARNED", ("2", "2"), {"-2": ("REFUTED IF STABLE", "not an answer if"), "2": ("EARNED", NOW)}),
    ("(x*x == 4) & ((x < 0) | (p & ~p))", "EARNED", ("-2", "-2"), {"-2": ("EARNED", NOW), "2": ("REFUTED IF STABLE", "not an answer if")}),
    ("(x*x == 4) & ((x > 0) | (p | ~p))", "EARNED", ("2", "2"), {"-2": ("EARNED IF STABLE", "an answer if"), "2": ("EARNED", NOW)}),
    # the other side: no dirty ground - as it always was
    ("x*x == 4", "EARNED", BOTH, {"-2": ("EARNED", NOW), "2": ("EARNED", NOW)}),
    ("(x*x == 4) & (x > 0)", "EARNED", ("2", "2"), None),      # (-2 is cut by the narrowing itself: one root reaches the judge)
    ("(x*x == 4) & (x > 5)", "REFUTED", None, {}),
    # no root holds now: the disposition speaks of the roots not refuted
    ("(x*x == 4) & p", "OPEN", BOTH, {"-2": ("OPEN", "not settled"), "2": ("OPEN", "not settled")}),
    ("(x*x == 4) & (p | ~p)", "EARNED IF STABLE", BOTH, {"-2": ("EARNED IF STABLE", "an answer if"), "2": ("EARNED IF STABLE", "an answer if")}),
    ("(x*x == 4) & (p & ~p)", "REFUTED IF STABLE", BOTH, {"-2": ("REFUTED IF STABLE", "not an answer if"), "2": ("REFUTED IF STABLE", "not an answer if")}),
    ("(x*x == 4) & ((x > 0) | (p & ~p)) & ((x < 0) | (p & ~p))", "REFUTED IF STABLE", BOTH, None),
    ("(x*x == 4) & ((x > 0) | (p & ~p)) & ((x < 0) | p)", "OPEN", BOTH, {"-2": ("REFUTED IF STABLE", "not an answer if"), "2": ("OPEN", "not settled")}),
    ("(x*x == 4) & ((x > 0) | (p | ~p)) & ((x < 0) | p)", "OPEN", BOTH, {"-2": ("EARNED IF STABLE", "an answer if"), "2": ("OPEN", "not settled")}),
    ("(x*x == 4) & ((x > 0) | (p | ~p)) & ((x < 0) | (p & ~p))", "EARNED IF STABLE", BOTH, {"-2": ("EARNED IF STABLE", "an answer if"), "2": ("REFUTED IF STABLE", "not an answer if")}),
]
for claim, disp, kept, roots in CASES:
    d, x, st, r = solve(claim)
    check(d == disp and x == kept, f"{claim}: {disp}, x in {kept}", (d, x))
    if roots is not None:
        check(set(st) == set(roots) and all(st[k][0] == roots[k][0] and st[k][1].startswith(roots[k][1]) for k in roots),
              f"{claim}: every root is said, with what it is", st)

# the defect, by name: never again the verdict of one root for the whole claim
d, x, st, r = solve("(x*x == 4) & ((x > 0) | (p & ~p))")
check(d != "REFUTED IF STABLE" and any("-2 is not an answer now" in ln for ln in r["log"]), "the defect of 8417ec8 is gone, and the log says what -2 is", (d, r["log"]))

# roots on credit are answers on credit (their value is T): the weakest of the answers
d, x, st, r = solve("(x*x == 4) & ((x > 0) | (b > 0))", "x=? credit, b=1 credit")
check(d == "ON CREDIT" and x == BOTH and st["-2"] == ("ON CREDIT", NOW) and st["2"] == ("EARNED", NOW), "an earned root beside a root on credit: both answers, ON CREDIT", (d, x, st))
d, x, st, r = solve("x*x == a", "x=? credit, a=4 credit")
check(d == "ON CREDIT" and x == BOTH, "both roots on credit: ON CREDIT, both kept", (d, x))

# a quantity that depends on the unknown follows the answer kept - and both answers where both are kept
d, x, st, r = solve("(x*x == 4) & ((x > 0) | p) & (y == x + 1)", "x=? credit, y=? credit")
y = r["solved"]["y"]
check(d == "EARNED" and x == ("2", "2") and (str(y["lo"]), str(y["hi"])) == ("3", "3"), "y = x + 1 follows the answer x = 2: y = 3", (d, x, y))
d, x, st, r = solve("(x*x == 4) & (y == x + 1)", "x=? credit, y=? credit")
y = r["solved"]["y"]
check(x == BOTH and (str(y["lo"]), str(y["hi"])) == ("-1", "3") and len(y.get("roots") or []) == 2, "both roots kept: y is -1 or 3", (x, y))

# THROUGH ZFL: the answer, and the root left is said (`roots_left`), never silently dropped
ROWS = [{"name": "x", "status": "unverified", "value": "?", "means": "x"}, {"name": "p", "status": "unverified", "means": "p"}]
def numeric(claim):
    r = zfl.run({"rows": ROWS, "claim": claim})
    assert r["ok"], r.get("issues")
    return r["report"]["numeric"]
n = numeric("(x*x == 4) & ((x > 0) | p)")
check(n["disposition"] == "EARNED" and n["solved"]["x"]["roots"] == ["2"] and n["verdict"] == "T"
      and [t["root"] for t in n["roots_left"]["x"]] == ["-2"] and "turns on verify p" in n["roots_left"]["x"][0]["answer"],
      "ZFL: EARNED, x = 2, and -2 is said with what it turns on", n)
n = numeric("(x*x == 4) & ((x > 0) | (p & ~p))")
check(n["disposition"] == "EARNED" and n["roots_left"]["x"][0]["disposition"] == "REFUTED IF STABLE", "ZFL: the defect's claim - EARNED, -2 not an answer if stable", n)
for claim in ("x*x == 4", "(x*x == 4) & (x > 0)", "x*x - 5*x + 6 == 0"):
    check("roots_left" not in numeric(claim), f"ZFL: nothing is left over for {claim} - no such field")

# SABOTAGE: the value of a root is not read (every root not refuted is kept, as before) - the open root weighs again
real = znumsolve._root_value
znumsolve._root_value = lambda w: None
try:
    d, x, st, r = solve("(x*x == 4) & ((x > 0) | p)")
finally:
    znumsolve._root_value = real
check(d == "OPEN" and x == BOTH, "PLANTED the value not read: the claim falls back to OPEN with both roots - the rule is what earns x = 2", (d, x))

print(f"{CHECKS} checks, {len(FAILS)} failed")
print("ROOT ANSWERS GREEN" if not FAILS else "ROOT ANSWERS RED")
sys.exit(1 if FAILS else 0)
