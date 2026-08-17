# -*- coding: utf-8 -*-
"""
Provenance semirings against this ledger — the same scenario, both formalisms.

The availability survey ended by naming what would settle the question it
could not: encode one scenario in a provenance system and in this ledger and
report what each answers. ProvSQL is a PostgreSQL extension and Postgres is
not on this machine, so what is compared here is the FORMALISM rather than the
package — provenance semirings (Green, Karvounarakis & Tannen, PODS 2007)
implemented directly, faithfully enough to be argued with.

The encoding is the standard one. Every source fact is a variable. A
conjunctive requirement multiplies; an alternative adds. A derived result
carries the polynomial that produced it. To ask what a withdrawal costs, set
that variable to zero and evaluate.

The expectation going in was that semirings would cover less of this ledger
than they do. They cover more, and the file says so.

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
    rows = [
        ("cascade on withdrawal", "yes", "yes",
         "the polynomial is the cascade"),
        ("alternatives (a|b)", "yes", "yes", "addition in the semiring"),
        ("who is exposed, by name", "yes", "yes", "the support of the poly"),
        ("HOW MUCH is exposed, by unit", "no", "yes",
         "semirings annotate, they do not carry magnitudes or units"),
        ("credit vs earned as a grade", "no", "yes",
         "an unsupported fact has the empty polynomial; there is no third "
         "status"),
        ("bracket for unverified independence", "no", "yes",
         "x+y assumes x and y distinct; nothing in the formalism decides it"),
        ("evidence vs authority", "no", "yes",
         "one semiring, one kind of edge"),
        ("refusing incommensurable units", "no", "yes", "not its subject"),
    ]
    print(f"    {'':38} {'semiring':>9} {'ledger':>7}")
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
    assert both_dead and not same_dead

    print("""
  WHAT THIS SETTLES, and it is against us on the larger half.

  Provenance semirings already do the cascade, already do alternatives,
  and already name the exposed set — three of the ledger's operations,
  published in 2007, with a maintained free implementation for
  PostgreSQL. Anyone needing those three should use ProvSQL and not this.

  What is left is narrower and, unlike a novelty claim, checkable: this
  ledger carries MAGNITUDES with units and refuses to add incommensurable
  ones; it grades a fact as earned or on credit rather than only
  supported or unsupported; it keeps evidence apart from authority; and
  it reports the unverifiability of an independence declaration as a
  bracket rather than leaving it implicit in the choice of variable
  names. None of those is a new idea. Together they are a different
  instrument for a different question — the auditor's `how much rests on
  this, and how sure are we allowed to be`, rather than the database's
  `which tuples produced this row`.

  AND THE HONEST WARNING. Four of the eight rows above are things a
  semiring could be extended to do — units and grades in a richer
  semiring, dimensions in a product of two. That nobody has packaged the
  extension is an availability fact with a shelf life, not a limit of
  the formalism.""")
    print("\nPROVENANCE PROBE GREEN — the older formalism covers more of this "
          "than expected.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
