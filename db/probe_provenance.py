# -*- coding: utf-8 -*-
"""
Provenance semirings against this ledger — the same scenario, both formalisms.

The availability survey ended by naming what would settle the question it
could not: encode one scenario in a provenance system and in this ledger and
report what each answers. This file implements provenance semirings (Green,
Karvounarakis & Tannen, PODS 2007) directly, faithfully enough to be argued
with, and runs the scenario through both.

The encoding is the standard one. Every source fact is a variable. A
conjunctive requirement multiplies; an alternative adds. A derived result
carries the polynomial that produced it. To ask what a withdrawal costs, set
that variable to zero and evaluate.

The expectation going in was that semirings would cover less of this ledger
than they do. They cover more, and the file says so.

AND THEN THE PACKAGE ITSELF WAS RUN, which moved the line again. An earlier
version of this file compared the formalism because Postgres was not on the
machine; it now is, and `db/provsql_ledger.sql` asks the same eight questions
of the shipped tool. One row of the table below was WRONG in consequence and
is corrected here: ProvSQL does carry magnitudes through aggregation, and
answers "what does the total become once inv-17 is withdrawn" exactly, with
`expected(sum(amount))` = 2000. Reasoning about what a formalism "does not
do" is not a substitute for installing it.

THE ENVIRONMENT LINE BELOW IS PRINTED HERE ON PURPOSE. The note quoted
"PostgreSQL 16.10" and this machine runs 16.14 — it never ran 16.10 — and the
error survived the repo's own orphan-figure scan because a version string had
been added to that scan's exemption list as harmless. An exemption added to
silence a false alarm is a place where a real one can hide. So the version
lives in ONE place, is printed by a stand CI runs, and `provsql_ledger.sql`
prints the LIVE `version()` beside it, so a machine that has moved on says so.

Run:  python3 db/probe_provenance.py
"""
import sys
from itertools import product

# ---------------------------------------------------------------- semirings
#
# A provenance polynomial over variable names. Represented as a set of
# monomials, each monomial a frozenset of variables — which is the semiring
# N[X] collapsed to B[X] (idempotent: x*x = x, x+x = x). Idempotence is the
# right choice here because a ground used twice is not used "twice".


# The environment of the ProvSQL measurements, recorded once. Anything that
# quotes a version quotes THIS, and `db/provsql_ledger.sql` prints the live
# `version()` next to its results so a drift is visible rather than assumed.
MEASURED_ON = ("measured on PostgreSQL 16.14 / ProvSQL 1.13.0-dev, "
               "2026-08-17")


def var(name):
    return {frozenset([name])}


def times(a, b):
    return {m | n for m in a for n in b} or set()


def plus(a, b):
    out = set(a) | set(b)
    # absorption: if one monomial's variables are a subset of another's, the
    # larger is redundant (x + xy = x)
    return {m for m in out if not any(o < m for o in out)}


def evaluate(poly, dead):
    """True if the result still stands when everything in `dead` is gone."""
    return any(not (m & dead) for m in poly)


def support(poly):
    return sorted({v for m in poly for v in m})


# ------------------------------------------------------- the same scenario
# Day one's ledger: three lines and a petty item, a ceiling, a payment; two
# derived figures above them. Two lines rest on ONE invoice.
SOURCES = {
    "line_a": ("inv17", 3000.0, "earned"),
    "line_b": ("inv17", 1500.0, "earned"),
    "line_c": ("inv18", 2000.0, "earned"),
    "quoted": (None, 1200.0, "credit"),
    "ceiling": ("contract", 9000.0, "earned"),
    "paid": (None, 5000.0, "credit"),
}


def build_polys():
    p = {}
    for name, (ground, _v, _s) in SOURCES.items():
        p[name] = var(ground) if ground else set()      # credit: no support
    p["billed"] = times(times(p["line_a"], p["line_b"]), p["line_c"])
    p["margin"] = times(p["billed"], p["paid"]) if p["paid"] else p["billed"]
    return p


QUESTIONS = [
    "1. What was spent in total?",
    "2. What is the whole ledger's total?",
    "3. Are we inside the ceiling?",
    "4. Which figures have never been documented?",
    "5. What rests on invoice inv-17?",
    "6. inv-17 is forged. What falls?",
    "7. What do the numbers become once it is withdrawn?",
    "8. May I quote the margin in the report?",
]


def main():
    print("=" * 78)
    print("PROVENANCE SEMIRINGS vs THIS LEDGER — same scenario, both ways")
    print("=" * 78)
    print(f"\n  {MEASURED_ON}")
    print("  (the single place this corpus records that environment; "
          "provsql_ledger.sql\n   prints the live version(), so a machine "
          "that has moved on contradicts it)")
    p = build_polys()

    print("\n  the polynomials, as a semiring system would carry them\n")
    for k in ("line_a", "billed", "margin", "quoted"):
        mono = " + ".join("·".join(sorted(m)) for m in sorted(
            p[k], key=lambda s: sorted(s))) or "(empty — no support)"
        print(f"    {k:9} {mono}")

    print("\n  1. WHAT THE SEMIRING ANSWERS AS WELL AS WE DO\n")
    fell = [k for k in ("line_a", "line_b", "line_c", "billed", "margin")
            if p[k] and not evaluate(p[k], {"inv17"})]
    print(f"       inv-17 forged, what falls: {', '.join(fell)}")
    print("     Identical to the ledger's cascade, and it needs no cascade:")
    print("     setting a variable to zero and evaluating IS the answer.")
    print("     Alternatives come free too — `inv17 + inv18` survives losing")
    print("     either, which is exactly this corpus's `|` and was in the")
    print("     literature in 2007. The expectation going in was that")
    print("     semirings covered less of this ledger than they do.")
    assert fell == ["line_a", "line_b", "billed", "margin"]

    print("\n  2. WHERE THE TWO ANSWER DIFFERENTLY\n")
    print("     The `ProvSQL` column is MEASURED on the installed package")
    print("     (see db/provsql_ledger.sql), not reasoned about.\n")
    rows = [
        ("cascade on withdrawal", "yes", "yes",
         "the polynomial is the cascade; set_prob(t,0) in the package"),
        ("alternatives (a|b)", "yes", "yes", "addition in the semiring"),
        ("who is exposed, by name", "yes", "yes", "the support of the poly"),
        ("HOW MUCH is exposed", "yes", "yes",
         "CORRECTED: expected(sum)=2000 after withdrawal, support(sum) "
         "brackets it [0,6500]"),
        ("...in a declared unit", "no", "yes",
         "sum() over 2000 EUR and 40 hours returned 2040, silently"),
        ("credit vs earned as a grade", "SHIPS", "yes",
         "REFUTED: sr_maxmin is a built-in (+ = enum-max, * = enum-min) over "
         "any ENUM — one CREATE TYPE and it grades our own ledger"),
        ("...and permission as a second grade", "SHIPS", "yes",
         "sr_minmax, demonstrated in their docs as Minimum Security "
         "Clearance — question 8"),
        ("bracket for unverified independence", "twice", "yes",
         "0.9900 by default; both ends computable — 0.99 and 0.90 — with ONE "
         "statement pointing one row's token at the other's"),
    ]
    print(f"    {'':38} {'ProvSQL':>9} {'ledger':>7}")
    for label, sem, led, why in rows:
        print(f"    {label:38} {sem:>9} {led:>7}   {why}")

    print("\n  3. THE ONE THAT IS NOT A DIFFERENCE OF POWER\n")
    print("       `inv17 + invoice17` — two names that may be one paper")
    both_dead = evaluate(plus(var("inv17"), var("invoice17")), {"inv17"})
    same_dead = evaluate(plus(var("inv17"), var("invoice17")),
                         {"inv17", "invoice17"})
    print(f"       survives losing inv17 alone       : {both_dead}")
    print(f"       survives losing both names        : {same_dead}")
    print("     The semiring gives the right answer to BOTH questions and")
    print("     no answer to the one in between: whether the two names are")
    print("     one paper. Neither formalism can. The difference is only")
    print("     that this ledger REPORTS the gap as a bracket and a named")
    print("     assumption, where a polynomial leaves it to whoever chose")
    print("     the variable names. That is a reporting decision, not a")
    print("     capability, and calling it a capability was the error the")
    print("     ledger note has now withdrawn.")
    print("\n     ON THE PACKAGE, measured rather than argued: ProvSQL renders")
    print("     this as `inv17 (+) invoice17`, evaluates it at 0.9900 from")
    print("     p=0.9 each, and reports probability_bounds [0.99, 0.99] — a")
    print("     point of zero width. If the two names are one piece of paper")
    print("     the figure is 0.9. Nothing in the output marks that the")
    print("     difference was assumed away; independence is the model's")
    print("     premise, not an oversight.")
    print("\n     AND THEN THE OBJECTION TO OUR OWN CLAIM WAS RUN, AND HELD.")
    print("     Encode the ledger twice — two names as two papers, then as")
    print("     one — and ProvSQL returns 0.9900 and 0.9000 itself. The")
    print("     bracket [0.90, 0.99] is COMPUTABLE THERE. What this ledger")
    print("     has is a DEFAULT, not a capability: it computes both readings")
    print("     unasked and refuses to print a bare number, where ProvSQL")
    print("     prints 0.9900 unless the reader knew to ask twice.")
    print("\n     AND EVEN THAT UNDERSTATED IT, per review: two encodings are")
    print("     not needed. Point the second row's provsql column at the")
    print("     first row's token — one UPDATE — and the same query returns")
    print("     0.9000. Their manual also states tuple-independence as a")
    print("     DEFAULT, not a limit ('correlations between tuples are not")
    print("     modelled. To model correlated probabilities, derive them")
    print("     explicitly with queries'), and ships repair_key for the")
    print("     block-independent-disjoint case, with tests.")
    assert both_dead and not same_dead

    print("""
  WHAT THIS SETTLES, and it is against us twice over.

  Provenance semirings already do the cascade, already do alternatives,
  and already name the exposed set. Published 2007, free implementation
  for PostgreSQL. Anyone needing those three should use ProvSQL.

  The installed package then took a fourth. It carries magnitudes
  through aggregation and returns the correct post-withdrawal total
  directly — `expected(sum(amount))` = 2000 — which this file previously
  said semirings do not do. That was reasoning where a measurement was
  available, and it was wrong.

  WHAT IS LEFT, after three rounds: NOTHING THAT IS OURS.

  This file said twice that the earned/credit grade was a semiring
  "nobody has written". It ships. `sr_maxmin` is a compiled built-in
  with + = enum-max and * = enum-min over any PostgreSQL ENUM, which is
  that lattice, and one CREATE TYPE grades the ledger above. Its dual
  `sr_minmax` ships too, demonstrated in their own documentation as
  Minimum Security Clearance — the permission dimension, question 8.
  Units are not a provenance question. The bracket is a default.

  THE SHAPE OF THE ERROR, since it recurred three times. Each round
  withdrew a claim and kept a remainder; each next round found the
  remainder was also available; and the reason is the same every time —
  a conclusion about what a tool does NOT do, reached by reasoning
  instead of by reading its function list. `\\df provsql.sr_*` would
  have ended this at the start.

  WHAT THAT MEASURES is distance, not just error: on this subject we are
  far enough from the frontier that an hour of checking finds another
  shipped feature, and there is no reason to expect a fourth round to
  end differently. The corpus keeps the comparison because it is true
  and reproducible, and claims nothing from it.""")
    print("\nPROVENANCE PROBE GREEN — the older formalism, and then the "
          "shipped package, cover more of this than expected.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
