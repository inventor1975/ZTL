# -*- coding: utf-8 -*-
"""
0^0, judged: two questions under one symbol — a VALUE (a convention) and a LIMIT (no subject).

Next to x/0 and 0/0 on the numeric floor (f0c71f8: a divisor 0 in every reading is E, "nothing to check"; 0/0 is
"a value must be stipulated"). Is 0^0 equal to 1, or undefined? Textbooks say both, and both are right — about
different things.

THE FORMALISATION, IN WORDS FIRST:
  value   "0^0", the operation at the point: the empty product. Algebra, combinatorics and power series fix it at
          1 (x^0 = 1 for every x, the binomial theorem, sum a_n x^n at x = 0, the number of maps from the empty
          set to itself). That is a CONVENTION — chosen because it keeps those laws whole, not found.
  limit   "the limit of x^y as (x, y) -> (0, 0)": along x^x it is 1, along 0^y (y > 0) it is 0, along x^0 it is 1,
          along x^(c / ln x) it is e^c — any positive number. The limit does not exist: the description "the limit"
          has no subject — E, as Perron's "largest natural number" (dilemmas/perron.py).

MEASURED HERE:
  1. four paths into (0, 0) and their limits, computed at x = 1e-12 (0^y, x^0 exact): 1, 0, 1, e^c for c = -1, 2;
  2. the numeric judge: "the value of 0^0", a convention with no laws chosen yet (any value in [0, inf)):
     "V == 1" OPEN, cure "stipulate V"; the convention of algebra stipulated (V = 1): EARNED;
  3. "the limit is 1": its subject is absent (the paths disagree) — E, and so is "the limit is 0";
  4. the same 1 is forced, not chosen, the moment a law is required: x^0 = 1 for all x > 0 extended to x = 0, and
     the count of maps from an empty set to an empty set (exactly one: the empty map) — the convention is the one
     that keeps the laws; another value breaks one of them (checked: V = 0 breaks the binomial expansion of
     (0 + 1)^2 written as sum C(2,k) 0^k 1^(2-k)).
WHAT E MEANS HERE (stated because a reviewer read it as "there is nothing to discuss"): E is the verdict on a claim
whose description has NO ADMISSIBLE READING — nothing answers to "the limit" or "the coat". It is the presupposition
failure of Frege and Strawson, and the empty-specification genre of the paradox docket (§5.1). It always comes with
its pair: the existence claim, which is not E but REFUTED. The question is real and answered (no limit; no coat);
what has no subject is the predication about the thing that is not there.
Run:  python3 dilemmas/zero_power_zero.py
"""
import math
import os
import sys
from itertools import product

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from ztljudge import judge                                    # noqa: E402
from znumjudge import judge_sheet_claim, parse_quantities      # noqa: E402


PATH_LIMITS = {}


def sec1_paths():
    print("-" * 72)
    print("1. FOUR PATHS INTO (0, 0), FOUR ANSWERS")
    x = 1e-12
    paths = {"x^x": x ** x, "0^y (y > 0)": 0.0 ** 1e-12, "x^0": x ** 0,
             "x^(-1/ln x)": x ** (-1 / math.log(x)), "x^(2/ln x)": x ** (2 / math.log(x))}
    want = {"x^x": 1.0, "0^y (y > 0)": 0.0, "x^0": 1.0, "x^(-1/ln x)": math.exp(-1), "x^(2/ln x)": math.exp(2)}
    for k, v in paths.items():
        assert abs(v - want[k]) < 1e-9 * max(1, want[k]) or abs(v - want[k]) < 1e-9, (k, v)
        print(f"   along {k:12s} -> {v:.6f}")
        PATH_LIMITS[k] = v
    print("   The limit at (0, 0) does not exist; along x^(c / ln x) every positive value is reached.")


def sec2_value_is_a_convention():
    print("-" * 72)
    print("2. THE VALUE OF 0^0 IS A CONVENTION")
    open_ = judge_sheet_claim("V == 1", *parse_quantities("V=[0,1000] earned:no-law-chosen convention"))
    fixed = judge_sheet_claim("V == 1", *parse_quantities("V=1 earned:empty-product convention"))
    assert open_["disposition"] == "OPEN" and open_["next_check"] == ["stipulate V"]
    assert fixed["disposition"] == "EARNED"
    print(f"   no law chosen yet: 'V == 1' {open_['disposition']}, cure {open_['next_check']}")
    print(f"   the empty-product convention stipulated: {fixed['disposition']}")


def sec3_the_limit_has_no_subject():
    print("-" * 72)
    print("3. 'THE LIMIT EXISTS' — REFUTED; 'THE LIMIT IS 1' — NO SUBJECT")
    # computed, not set by hand: the paths of section 1 disagree, so there is no limit to speak of
    vals = list(PATH_LIMITS.values())
    mark = "E" if max(vals) - min(vals) > 1e-6 else "T"
    ex = judge("limit_exists", {"limit_exists": "F" if mark == "E" else "T"})
    assert ex["disposition"] == "REFUTED"
    print(f"   limit_exists: {ex['disposition']} — the question is real, and answered: the paths disagree")
    for claim in ("limit_is_1", "limit_is_0"):
        r = judge(claim, {claim: mark})
        assert r["disposition"] == "E"
        print(f"   {claim}: {r['disposition']} — nothing answers to 'the limit' (presupposition failure)")


def sec4_the_laws_force_one():
    print("-" * 72)
    print("4. WHY 1: THE CONVENTION THAT KEEPS THE LAWS")
    # maps from the empty set to the empty set: exactly one (the empty map) — |B|^|A| with |A| = |B| = 0
    maps = list(product([], repeat=0))
    assert len(maps) == 1
    for V in (0, 1):
        def pw(a, k):
            return V if (a == 0 and k == 0) else a ** k
        lhs = (0 + 1) ** 2
        rhs = sum(math.comb(2, k) * pw(0, k) * pw(1, 2 - k) for k in range(3))
        print(f"   V = {V}: binomial (0 + 1)^2 = {lhs}, as a sum of terms = {rhs}" + ("  (broken)" if lhs != rhs else ""))
        assert (lhs == rhs) == (V == 1)
    print("   one map from the empty set to itself; V = 1 keeps the binomial theorem, V = 0 breaks it.")


if __name__ == "__main__":
    for sec in (sec1_paths, sec2_value_is_a_convention, sec3_the_limit_has_no_subject, sec4_the_laws_force_one):
        sec()
    print("-" * 72)
    print("ZERO TO THE ZERO: all measurements hold.")
