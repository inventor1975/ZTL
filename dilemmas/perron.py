# -*- coding: utf-8 -*-
"""
Perron's paradox, judged: "the largest natural number" names nothing.

Oskar Perron's example ("Zur Existenzfrage eines Maximums oder Minimums", Jahresbericht der DMV 22, 1913, 140-144; the point he made against assuming that an
extremum exists before proving it, in the calculus of variations): "Let N be the largest natural number. If N > 1,
then N^2 > N, so N was not the largest. Hence N = 1." Every step is valid; the conclusion is absurd.

THE FORMALISATION, IN WORDS FIRST — a bad skeleton refutes a straw man:

  exists      "there is a largest natural number"                  — a claim about the naturals;
  step        "if N is the largest, then N^2 <= N, so N = 1"         — Perron's derivation, valid;
  the_is_one  "the largest natural number is 1"                       — a sentence with a description in it;
  one_is_max  "1 is the largest natural number"                       — a different sentence, about 1.

  "The largest natural number is 1" has two classical readings, and the century-old dispute about them is
  Russell's against Frege's and Strawson's ("the present king of France is bald"):
    Russell     it ASSERTS existence: "there is exactly one largest, and it is 1"  — false if nothing is largest;
    Frege/Strawson  it PRESUPPOSES existence: with nothing to refer to, it is neither true nor false.
  ZTL keeps both, as two claims with two verdicts, instead of choosing between them: Russell's reading is a
  conjunction whose first conjunct is refuted; the presupposition reading is a claim whose subject is absent — E.

MEASURED HERE (each section asserts what it prints):

  1. existence is refuted, by the numeric floor itself: "N >= N + 1" over the naturals (N an int, unbounded) is
     REFUTED in every reading — no N is at least every natural; and in each finite segment {1..B} the largest is B,
     whose square leaves the segment for every B >= 2, so Perron's step never applies inside one;
  2. the conditional "if a largest exists, it is 1" is EARNED — vacuously, since exists is refuted; classical logic
     agrees, and this is not where the paradox lives;
  3. the two readings of "the largest natural number is 1": Russell's (exists & is 1) REFUTED; the presupposition
     reading (the subject absent) E — not false, nothing to check. "1 is the largest natural number" is a different
     claim and REFUTED, with the witness 2;
  4. control: where a largest element DOES exist — the squaring-closed set {0, 1} — the same derivation earns its
     conclusion: exists earned, the step valid, N = 1 EARNED. Perron's argument is sound exactly where existence is
     established first, which was his point.

NOT CLAIMED: which reading of a description is "right" — the judge prices both.

Run:  python3 dilemmas/perron.py
"""
import os
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from ztljudge import judge                                    # noqa: E402
from znumjudge import judge_sheet_claim, parse_quantities      # noqa: E402


def exists_mark():
    """the mark of 'there is a largest natural', COMPUTED, not set by hand: refuted iff the numeric floor refutes
    'N >= N + 1' over the naturals (the instance m = N + 1 of 'N is at least every m')"""
    r = judge_sheet_claim("N >= N + 1", *parse_quantities("N=? int"))
    return {"REFUTED": "F", "EARNED": "T"}.get(r["disposition"], "Z")


def description_mark(exists, value):
    """the presupposition reading (Frege/Strawson): a sentence about 'the F' has the value of its predication when
    the F exists, and NO SUBJECT (E) when it does not — the rule, stated once"""
    return "E" if exists == "F" else value


def sec1_no_largest():
    print("-" * 72)
    print("1. NO LARGEST NATURAL NUMBER — REFUTED BY THE NUMERIC FLOOR")
    r = judge_sheet_claim("N >= N + 1", *parse_quantities("N=? int"))
    assert r["disposition"] == "REFUTED", r
    print(f"   'N >= N + 1' over the naturals: {r['disposition']} — no N is at least every natural")
    inside = [b for b in range(1, 51) if b * b <= b]
    assert inside == [1]
    print("   in each segment {1..B}, B = 1..50, the largest is B, and B^2 stays inside only for B = 1:")
    print("   Perron's step never applies within a segment where a largest exists, except at {1}")


def sec2_vacuous_conditional():
    print("-" * 72)
    print("2. 'IF A LARGEST EXISTS, IT IS 1' — EARNED, VACUOUSLY")
    r = judge("exists -> is_one", {"exists": exists_mark(), "is_one": "Z"})
    assert r["disposition"] == "EARNED"
    print(f"   exists refuted: {r['disposition']} — true because nothing satisfies the antecedent")


def sec3_two_readings():
    print("-" * 72)
    print("3. 'THE LARGEST NATURAL NUMBER IS 1' — TWO READINGS, TWO VERDICTS")
    ex = exists_mark()
    russell = judge("exists & is_one", {"exists": ex, "is_one": "Z"})
    frege = judge("the_is_one", {"the_is_one": description_mark(ex, "Z")})
    # '1 is the largest' is about 1, and the numeric floor checks it at the witness 2
    w = judge_sheet_claim("one >= two", *parse_quantities("one=1 earned:n, two=2 earned:n"))
    other = judge("one_is_max", {"one_is_max": {"REFUTED": "F", "EARNED": "T"}.get(w["disposition"], "Z")})
    assert russell["disposition"] == "REFUTED" and frege["disposition"] == "E"
    assert other["disposition"] == "REFUTED"
    print(f"   Russell (asserts existence):            {russell['disposition']}")
    print(f"   Frege/Strawson (presupposes existence): {frege['disposition']} — the subject is absent, nothing to check")
    print(f"   '1 is the largest natural number':      {other['disposition']} — the witness is 2")
    print("   The paradox spends the description as if it had a subject: the proof's conclusion is about nothing.")


def sec4_control_existence_first():
    print("-" * 72)
    print("4. CONTROL — WHERE A LARGEST EXISTS, PERRON IS RIGHT")
    S = {0, 1}
    assert all(x * x in S for x in S) and max(S) == 1      # closed under squaring, and it has a largest element
    top = max(S)
    ex = "T"                                               # established by inspection of a finite set
    is_one = "T" if (top * top <= top and top >= 1 and top == 1) else "F"     # Perron's step, at the actual top
    r = judge("exists & (exists -> is_one)", {"exists": ex, "is_one": is_one})
    assert r["disposition"] == "EARNED"
    print(f"   {{0, 1}}, closed under squaring: the largest exists (1); the same derivation: {r['disposition']}")
    print("   Prove existence first, then use the extremum — Perron's lesson, as a verdict.")


if __name__ == "__main__":
    for sec in (sec1_no_largest, sec2_vacuous_conditional, sec3_two_readings, sec4_control_existence_first):
        sec()
    print("-" * 72)
    print("PERRON: all measurements hold.")
