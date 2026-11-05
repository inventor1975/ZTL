# -*- coding: utf-8 -*-
"""
0.999... = 1, judged: the number the decimal names, and the process of writing it, are two different objects.

"0.999... never reaches 1" and "0.999... = 1" are both said with conviction; both are true — of different things.

THE FORMALISATION, IN WORDS FIRST:
  the TERMS    0.9, 0.99, 0.999, ...: every one of them is less than 1 (the process — VR's register of becoming);
  the VALUE    what the infinite decimal NAMES: by the definition of decimal notation, the least number not below
               any term (the supremum, the limit) — and that is 1 (the done object).
  Which object "0.999..." refers to is fixed by the notation's definition; no inspection of finitely many digits can
  decide "= 1" against "< 1". The numeric judge shows exactly that: after k digits the value is only known to lie in
  [1 - 10^-k, 1], and "value < 1" stays OPEN for every k; the definition (stipulated) makes "value == 1" EARNED.

MEASURED HERE:
  1. every term 1 - 10^-k (k = 1..60) is below 1, exactly — "the terms never reach 1": EARNED;
  2. for every bound 10^-j (j = 1..60) a term is closer to 1 than that — no number below 1 bounds the terms above,
     so the least upper bound is 1, exactly in rationals;
  3. the judge after k = 1, 10, 50 digits: "value < 1" OPEN, cure "stipulate value" (the notation's definition),
     "value >= 0.9" EARNED; with the definition stipulated (value = 1): "value == 1" EARNED, "value < 1" REFUTED;
  4. the classical check, 3 x 0.333... : the terms 3 x (1/3 - 10^-k/3) = 1 - 10^-k — the same terms, the same value.
Run:  python3 dilemmas/point_nine.py
"""
import os
import sys
from fractions import Fraction as Fr

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from znumjudge import judge_sheet_claim, parse_quantities      # noqa: E402


def term(k):
    return 1 - Fr(1, 10 ** k)


if __name__ == "__main__":
    print("-" * 72)
    print("1. THE TERMS: ALL BELOW 1")
    assert all(term(k) < 1 for k in range(1, 61))
    print("   1 - 10^-k < 1 for k = 1..60, exactly")
    print("-" * 72)
    print("2. THE VALUE: THE LEAST UPPER BOUND IS 1")
    for j in range(1, 61):
        assert term(j + 1) > 1 - Fr(1, 10 ** j)          # a term beats every candidate bound below 1
    print("   for every 10^-j, j = 1..60, some term lies within it of 1: nothing below 1 bounds the terms")
    print("-" * 72)
    print("3. THE JUDGE: FINITELY MANY DIGITS DECIDE NOTHING; THE DEFINITION DOES")
    for k in (1, 10, 50):
        sheet = f"value=[{1 - Fr(1, 10 ** k)},1] earned:digits convention"
        lt = judge_sheet_claim("value < 1", *parse_quantities(sheet))
        ge = judge_sheet_claim("value >= 9/10", *parse_quantities(sheet))
        assert lt["disposition"] == "OPEN" and lt["next_check"] == ["stipulate value"]
        assert ge["disposition"] == "EARNED"
        print(f"   after {k:2d} digits: 'value < 1' {lt['disposition']} {lt['next_check']}; 'value >= 0.9' {ge['disposition']}")
    d = parse_quantities("value=1 earned:decimal-notation convention")
    assert judge_sheet_claim("value == 1", *d)["disposition"] == "EARNED"
    assert judge_sheet_claim("value < 1", *d)["disposition"] == "REFUTED"
    print("   the notation's definition stipulated: 'value == 1' EARNED, 'value < 1' REFUTED")
    print("-" * 72)
    print("4. 3 x 0.333...")
    assert all(3 * (Fr(1, 3) - Fr(1, 3 * 10 ** k)) == term(k) for k in range(1, 61))
    print("   3 x (k threes) = 1 - 10^-k, term by term: the same sequence, so the same value")
    print("-" * 72)
    print("POINT NINE: all measurements hold.")
