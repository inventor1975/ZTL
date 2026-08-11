# -*- coding: utf-8 -*-
"""
The paradox does not eat the invoice: containment on a working sheet.

The curator's point, checked rather than repeated: a classical engine —
Z3, or any SAT/SMT solver, or plain classical logic — answers globally
and in one bit. Feed it a sheet with ONE circular sign-off and the whole
sheet is `unsat`; and from an unsatisfiable set classical logic entails
EVERYTHING, so the same sheet "proves" the total is 4500 and that it is
9999. The engine is not wrong. It is answering the only question it has:
is there a world where all of this holds at once.

An auditor cannot work with that answer. The circular note is one cell of
a sheet with twenty honest lines, and those lines still have to be
judged. This stand measures the difference on a sheet that mixes both:
plain numeric claims and a self-referential pair of the kind that
actually occurs in sign-offs ("the summary is right iff line 3 is right;
line 3 is right iff the summary is not").

  classically  the premises have NO model, so every query is entailed —
               including two contradictory ones. Usable verdicts: none,
               and the failure is silent: the engine says nothing is
               wrong with asking.
  here         the circular pair is quarantined by the passport (0
               models, refusal permanent) and the numbers keep their own
               verdicts, each with its own warranty and cure.

That is what the numeric floor buys that an engine does not: the numbers
and the sick cell live on the same sheet, and only the sick cell stops.

Run:  python3 zcontain.py
"""
import os
import sys
from itertools import product

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from ztl import T, F, Z                                       # noqa: E402
from zpassport import passports                               # noqa: E402
from znumjudge import judge_sheet_claim, parse_quantities      # noqa: E402

# the sheet: three honest numeric claims and one circular sign-off
SHEET = [
    ("lines_add_up", "sum(line1,line2,line3) == total",
     "line1=1000 earned:inv-17, line2=2000 earned:inv-18, "
     "line3=1500 earned:inv-19, total=4500 earned:contract"),
    ("under_budget", "total <= budget",
     "total=4500 earned:contract, budget=5000 earned:order-o4"),
    ("vat_line", "vat == total / 5",
     "vat=900 earned:inv-20, total=4500 earned:contract"),
]

# the circular pair, as it appears in a real sign-off
# Jourdain's shape, which is what a circular sign-off actually is: the
# summary is right exactly when line 3 is, and line 3 is right exactly
# when the summary is NOT. (The first draft of this file used a different
# circle that turned out to be merely DETERMINED — one model, s = False —
# and the passport said so before any prose was written.)
CIRCLE = {"summary_ok": "line3_ok",
          "line3_ok": ("not", "summary_ok")}


def sec1_the_classical_answer():
    print("-" * 72)
    print("1. THE CLASSICAL ANSWER: one bit, and then anything at all")
    # premises: the circular pair as material equivalences
    atoms = ["summary_ok", "line3_ok"]
    models = []
    for vals in product((True, False), repeat=2):
        s, l = vals
        if (s == l) and (l == (not s)):
            models.append(vals)
    print(f"   models of the sign-off pair: {len(models)}")
    assert models == []
    print("   none — so the premises are unsatisfiable, and from an")
    print("   unsatisfiable set classical logic entails every sentence.")
    for query in ("total == 4500", "total == 9999"):
        print(f"     entailed by the sheet: {query}   (vacuously, and so is")
        print(f"       its negation)")
    print("   an engine reports `unsat` and stops. Nothing on the sheet is")
    print("   judged, the twenty honest lines included, and the report does")
    print("   not say which line poisoned the well.")


def sec2_the_contained_answer():
    print("-" * 72)
    print("2. HERE: the sick cell is named, and the sheet goes on")
    reports = {tuple(sorted(c)): (k, w) for c, k, w in passports(CIRCLE)[1]}
    for comp, (kind, why) in sorted(reports.items()):
        print(f"   {'/'.join(comp):24}: {kind:9} — {why}")
    assert any(k == "PARADOX" for k, _ in reports.values())
    judged = 0
    for label, formula, data in SHEET:
        q, m = parse_quantities(data)
        r = judge_sheet_claim(formula, q, m)
        judged += r["disposition"] in ("EARNED", "REFUTED", "ON CREDIT",
                                       "OPEN")
        print(f"   {label:14} {r['disposition']:9} "
              f"{('cure ' + str(r['next_check'])) if r['next_check'] else ''}")
    assert judged == len(SHEET)
    print(f"   {judged} of {len(SHEET)} numeric claims still judged, each on")
    print("   its own ground, while the circular pair sits in quarantine")
    print("   with its passport: no classical model, refusal permanent.")


def sec3_the_claim_that_touches_it():
    print("-" * 72)
    print("3. AND THE ONE CLAIM THAT DOES TOUCH THE SICK CELL")
    q, m = parse_quantities("total=4500 earned:contract, budget=5000 "
                            "earned:order-o4, summary_ok=Z")
    r = judge_sheet_claim("total <= budget & summary_ok", q, m)
    print(f"   'under budget AND the summary is signed off': "
          f"{r['disposition']} — verify {r['core']['unverified']}")
    assert r["disposition"] == "OPEN"
    assert r["core"]["unverified"] == ["summary_ok"]
    print("   OPEN, and the weak link is named. Not `unsat`, not silence,")
    print("   and not a verdict borrowed from a poisoned well: the claim")
    print("   that leans on the sick cell is the only one that waits.")


if __name__ == "__main__":
    print("=" * 72)
    print("CONTAINMENT — the paradox does not eat the invoice")
    print("=" * 72)
    sec1_the_classical_answer()
    sec2_the_contained_answer()
    sec3_the_claim_that_touches_it()
    print("=" * 72)
    print("ZCONTAIN GREEN — a classical engine answers the sheet in one")
    print("bit and, being unsatisfiable, licenses both 4500 and 9999. Here")
    print("the circular sign-off is classified (no model, permanent) and")
    print("quarantined, every numeric claim keeps its own verdict and cure,")
    print("and the single claim that leans on the sick cell is the single")
    print("one that waits. This is what the numeric floor buys that a")
    print("solver does not: the numbers and the paradox on one sheet, with")
    print("only the paradox stopping.")
