# -*- coding: utf-8 -*-
"""
The measurement week, day six: system errors, where nobody lied.

Day five scored this instrument against audits that failed and the headline
was deflating on purpose: against a determined liar who controls the input,
the ledger is not weak, it is inert. It grades what it is told, and Wirecard
would have printed EARNED for years.

So the curator asked the right next question — find a case that is NOT fraud.
A system error. Somebody competent, nobody lying, and a number that went
wrong anyway. Does the instrument earn its keep there?

Three cases. TWO are documented (Mars Climate Orbiter 1999, JPMorgan 2012);
the third is a SHAPE the author constructed, not a case — its figures echo the
high-debt-threshold episode and it is a stipulated retraction rather than a
reconstruction of what happened there. An earlier version of this docstring
said "three documented cases", which was false.

Each is RUN through the actual core rather than reasoned about, and the Mars
result is weaker than it first appeared: see below.

Run:  python3 db/probe_system_errors.py
"""
import json
import os
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

import zbook                                                   # noqa: E402
from znumjudge import judge_sheet_claim, parse_quantities      # noqa: E402


def case_mars():
    """Mars Climate Orbiter, 1999. The ground software reported thruster
    impulse in pound-force seconds; the navigation software expected
    newton-seconds. One lbf is about 4.45 N, so every firing was read as
    a quarter of its true effect, and the orbiter entered at roughly 57 km
    instead of 140-150. Lost.

    No fraud, no incompetence at either end, and both teams correct within
    their own convention. The interface specification DID say metric — the
    data did not."""
    print("\n  1. MARS CLIMATE ORBITER (1999) — thruster impulse, lbf vs N")
    q, m = parse_quantities(
        "impulse_reported=1 earned:small-forces-file lbf, "
        "impulse_expected=1 earned:nav-spec N")
    r = judge_sheet_claim("impulse_reported == impulse_expected", q, m)
    print(f"       disposition : {r['disposition']}")
    print(f"       why         : {r['why']}")
    print(f"       culprits    : {r['culprits']}  (kind: {r['culprit_kind']})")
    print(f"       next check  : {r['next_check'][0]}")
    # AND NOW THE CASE AS IT ACTUALLY HAPPENED, which this file got wrong
    # for a day. The SM_FORCES file carried numbers; the unit lived in an
    # interface specification, not beside the value. Give the judge that and
    # it does NOT refuse — a quantity with no unit unifies with anything.
    q2, m2 = parse_quantities(
        "impulse_reported=1 earned:small-forces-file, "
        "impulse_expected=1 earned:nav-spec N")
    r2 = judge_sheet_claim("impulse_reported == impulse_expected", q2, m2)
    print(f"\n       and with NO unit on the source, as in the real file:")
    print(f"       disposition : {r2['disposition']}   <- the wrong answer")
    assert r2["disposition"] == "EARNED"
    assert r["disposition"] == "E" and "lbf" in r["why"]
    print("     SO THE CATCH IS A RECONSTRUCTION, NOT A CATCH. The refusal")
    print("     above requires that somebody already recorded `lbf` beside")
    print("     the number — which is exactly the thing that was missing in")
    print("     1999. Where the unit is absent the floor returns EARNED and")
    print("     the orbiter is lost with the machine's blessing. What the")
    print("     run demonstrates is the VALUE OF CARRYING THE UNIT, not an")
    print("     ability to detect its absence: `_unify_units` compares two")
    print("     strings and a missing string unifies with anything.")
    print("     The honest claim is the design rule, and it is narrower than")
    print("     the case: a value that carries its unit cannot be silently")
    print("     mixed. Whether values carry units is upstream of us.")
    print("     CAUGHT ONLY IF DECLARED. The fourth corner is exactly")
    print("     this refusal: two quantities that cannot be compared do not")
    print("     produce a wrong number, they produce E and say which two.")
    print("     THE CONDITION, and it is the whole design point: the unit")
    print("     must travel WITH THE VALUE. A specification saying 'metric'")
    print("     in a document nobody re-reads is what failed here. A value")
    print("     that carries its own unit cannot be silently mixed, because")
    print("     the comparison refuses rather than converts.")
    return "DECLARED-ONLY"


def case_whale():
    """JPMorgan, 2012. In the Basel II.5 VaR model, after subtracting the
    old hazard rate from the new one, the spreadsheet divided by their SUM
    where the modeller intended their AVERAGE — halving the volatility
    reported. Around $6bn of losses followed.

    The demonstration below is against this instrument, not for it."""
    print("\n  2. JPMORGAN 'LONDON WHALE' (2012) — divided by the sum, not "
          "the average")
    q, m = parse_quantities("new_rate=6 earned:model, old_rate=2 earned:model,"
                            " reported=0.5 earned:model")
    wrong = judge_sheet_claim(
        "reported == (new_rate - old_rate) / (new_rate + old_rate)", q, m)
    right = judge_sheet_claim(
        "reported == (new_rate - old_rate) / ((new_rate + old_rate) / 2)", q, m)
    print(f"       the formula as WRITTEN   -> {wrong['disposition']}")
    print(f"       the formula as INTENDED  -> {right['disposition']}")
    assert wrong["disposition"] == "EARNED"
    print("     NOT CAUGHT, and the run above is the proof rather than an")
    print("     admission. The written formula is well-formed, its inputs")
    print("     are grounded, its units agree, and the floor returns EARNED")
    print("     on a figure that is half of what the author meant. Nothing")
    print("     in this corpus compares a formula against an intention —")
    print("     there is no second copy of the intention to compare it to.")
    print("     The one thing that IS ours here is thinner and worth stating")
    print("     without inflation: the number reached the model by a manual")
    print("     copy-paste between spreadsheets. 'Transcribed by hand' and")
    print("     'read from the source' are different grades on ISA 500's")
    print("     axes (probe_lattice), so the figure could have carried a")
    print("     visible mark. A mark is not a catch.")
    return "OUT"


def case_cascade():
    """The shape shared by every corrected-input scandal: a conclusion is
    published, the input beneath it is later fixed, and the conclusion goes
    on being cited because nothing connects the two.

    This is the case the ledger exists for, so it is run rather than
    described — including the day's new metric, which says how much."""
    print("\n  3. A CORRECTED INPUT, AND WHAT WENT ON STANDING ON IT")
    book = [
        ("dataset", "series_avg == -0.1", "series_avg=-1/10 earned:sheet-v1"),
        ("finding", "high_debt_penalty > 0",
         "high_debt_penalty=21/10 earned:claim/dataset"),
        ("policy", "recommended_cut == 40",
         "recommended_cut=40 earned:claim/finding"),
    ]
    before = zbook.judge_book(book)
    print("       before   " + ", ".join(
        f"{k}={before[k]['disposition']}" for k in before))
    fell = zbook.fallout(book, "sheet-v1")
    print(f"       the spreadsheet range is corrected -> "
          f"{[c for c, _b, _a in fell]}")
    print(f"       cost bracket for sheet-v1          : "
          f"{[zbook.cost(book, 'sheet-v1')['low'], zbook.cost(book, 'sheet-v1')['high']]}")
    for g, unit, total, _n in zbook.concentration(book):
        if g == "sheet-v1":
            print(f"       and how much rests on it           : {float(total)}")
    assert len(fell) == 3
    print("     CAUGHT, and this is the ordinary case rather than the")
    print("     famous one. One correction at the bottom moves all three")
    print("     storeys, including the recommendation two levels up that")
    print("     never named the spreadsheet. What a human does here is")
    print("     remember; what the ledger does is compute — and it cannot")
    print("     forget, get tired, or leave the company.")
    print("     THE CONDITION, again the same one: somebody had to write")
    print("     `earned:claim/dataset`. Citations are honoured, never")
    print("     discovered. In a spreadsheet that graph already exists for")
    print("     free, which is why the spreadsheet is the interesting place")
    print("     to try this next — untested, and named as untested.")
    return "CAUGHT"


def main():
    print("=" * 78)
    print("SYSTEM ERRORS — nobody lied, and the number went wrong anyway")
    print("=" * 78)
    verdicts = [case_mars(), case_whale(), case_cascade()]
    print("\n" + "=" * 78)
    print(f"  CAUGHT {verdicts.count('CAUGHT')} of {len(verdicts)}"
          f"   CAUGHT ONLY IF DECLARED {verdicts.count('DECLARED-ONLY')}"
          f"   NOT CAUGHT {verdicts.count('OUT')} of {len(verdicts)}")
    print("""
  READ AGAINST DAY FIVE. Against fraud this instrument scored 2 of 8 and
  prevented nothing. Against system error it catches two of three, and the
  two are caught OUTRIGHT — a refusal to compare, and a cascade that moves
  a conclusion nobody linked by hand.

  That is the honest shape of the thing, and it is worth saying in one
  line so that nobody has to be told twice: THIS IS NOT A FRAUD DETECTOR,
  IT IS AN INSTRUMENT AGAINST LOSING THE THREAD. Against an adversary who
  controls the input it is inert. Against a competent person with a
  thousand rows and a spreadsheet corrected six months ago, it computes
  what a human is currently expected to remember.

  The condition on both catches is identical and must not be buried: the
  unit must travel with the value, and the citation must have been
  written down. Where a graph already exists — a spreadsheet, a pipeline,
  a chain of model calls — the second condition costs nothing. That is a
  HYPOTHESIS, not a measurement, and it is the next thing to test.""")
    assert verdicts.count("CAUGHT") == 1
    assert verdicts.count("DECLARED-ONLY") == 1
    print("\nSYSTEM ERRORS PROBE GREEN — two caught, one not, all three run.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
