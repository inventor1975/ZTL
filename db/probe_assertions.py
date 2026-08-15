# -*- coding: utf-8 -*-
"""
The measurement week, day two: somebody ELSE's list.

`probe_ledger.py` ends by naming its own weakness — the eight questions were
written by the person the answers flatter. This file replaces them with the
profession's own list, taken from the auditing standards rather than from
this corpus's vocabulary:

  * the assertion list of ISA 315 as stated by ACCA — six for classes of
    transactions, six for balances, quoted verbatim below;
  * eight concrete accounts-payable procedures from an audit programme;
  * the evidence-reliability hierarchy of ISA 500.

The third turned out to matter most, and not in the direction expected. The
profession already ranks evidence, and it ranks it along FOUR axes, not one.
Our `earned` / `credit` is a two-point collapse of a lattice somebody else
built for the same purpose sixty years earlier.

Run:  python3 db/probe_assertions.py
"""
import itertools
import sys

# ------------------------------------------------------------------------
# PART 1 — the twelve assertions, verbatim, and what each needs
#
# verdict:
#   PLAIN     an ordinary schema answers it; we add nothing
#   WARRANT   needs the status/witness beside the value
#   NEITHER   no ledger answers it, ours included — the evidence is outside
# ------------------------------------------------------------------------
ASSERTIONS = [
    ("Occurrence", "transactions and events that have been recorded or "
     "disclosed have occurred", "WARRANT",
     "'has occurred' is precisely a claim about the ground, not the amount"),
    ("Completeness (transactions)", "all transactions and events that should "
     "have been recorded have been recorded", "NEITHER",
     "THE hardest one, and no database can touch it: the missing invoice is "
     "missing. Absence of a row is not evidence of absence of a liability, "
     "and our warrant column says nothing about rows that are not there"),
    ("Accuracy", "amounts and other data relating to recorded transactions "
     "have been recorded appropriately", "PLAIN",
     "arithmetic against a source document — ordinary SQL, ordinary joins"),
    ("Cut-off", "transactions and events have been recorded in the correct "
     "accounting period", "PLAIN",
     "a date comparison. We have a logical-time module and it is the wrong "
     "instrument: accounting periods are calendar facts, not epochs"),
    ("Classification (transactions)", "transactions and events have been "
     "recorded in the proper accounts", "PLAIN",
     "a foreign key to a chart of accounts"),
    ("Presentation (transactions)", "transactions and events are "
     "appropriately aggregated or disaggregated and clearly described",
     "PLAIN", "a reporting concern"),
    ("Existence", "assets, liabilities and equity interests exist", "WARRANT",
     "the same shape as Occurrence: what stands behind the row"),
    ("Rights and obligations", "the entity holds or controls the rights to "
     "assets, and liabilities are the obligations", "WARRANT",
     "a contract is a ground, and losing it is a retraction"),
    ("Completeness (balances)", "all assets, liabilities and equity interests "
     "that should have been recorded have been recorded", "NEITHER",
     "same absence problem"),
    ("Accuracy, valuation and allocation", "assets, liabilities and equity "
     "interests have been included at appropriate amounts", "WARRANT",
     "an estimate and a measurement are both numbers in the column; only "
     "the warrant separates them"),
    ("Classification (balances)", "assets, liabilities and equity interests "
     "have been recorded in proper accounts", "PLAIN", "a foreign key"),
    ("Presentation (balances)", "assets, liabilities and equity interests are "
     "appropriately aggregated or disaggregated", "PLAIN", "reporting"),
]

# The eight procedures of an accounts-payable programme, with the same test.
PROCEDURES = [
    ("check register after period end, payments over a threshold vs invoices",
     "PLAIN"),
    ("compare expenses to budget, investigate unexplained variances",
     "PLAIN"),
    ("detailed analysis of specific expense accounts", "PLAIN"),
    ("sort by vendor, scan for duplicate payments of identical amounts",
     "PLAIN"),
    ("aged payable detail at period end, verify unusual or outdated items",
     "PLAIN"),
    ("review subsequent invoices for payables wrongly in or out", "PLAIN"),
    ("inquire about unrecorded invoices", "NEITHER"),
    ("targeted fraud procedures where controls are weak", "WARRANT"),
]


# ------------------------------------------------------------------------
# PART 2 — ISA 500's reliability hierarchy, as an actual partial order
#
# The standard does not give a scale; it gives comparisons, and they run
# along independent axes:
#     external source        > internal
#     documentary            > oral
#     original               > photocopy or digitised copy
#     obtained by the auditor directly > obtained by inference
#
# Componentwise, which makes it a LATTICE and not a ladder — and that is the
# finding. Two grounds can be INCOMPARABLE: an external oral statement and an
# internal original document, neither above the other. A binary
# earned/credit cannot hold that, and neither can any single number.
# ------------------------------------------------------------------------
AXES = ("external", "documentary", "original", "direct")


def dominates(a, b):
    return all(x >= y for x, y in zip(a, b))


def meet(a, b):
    """The greatest lower bound — what a total inherits from its parts.

    `honest_sum` in probe_ledger takes the weakest part. In a lattice the
    right operation is the meet, and it differs: the meet of two INCOMPARABLE
    grades is strictly below BOTH. A total assembled from an external oral
    figure and an internal written one is worse than either of them, which
    is exactly what an auditor means by a mixed-quality balance and exactly
    what a two-valued column cannot express."""
    return tuple(min(x, y) for x, y in zip(a, b))


def name(g):
    return "/".join(ax if v else "not-" + ax for ax, v in zip(AXES, g))


def main():
    print("=" * 78)
    print("SOMEBODY ELSE'S LIST — the profession's own questions")
    print("=" * 78)

    from collections import Counter
    c = Counter(v for _n, _d, v, _w in ASSERTIONS)
    print("\n  The twelve assertions of ISA 315 (ACCA's statement of them):\n")
    for n, d, v, why in ASSERTIONS:
        print(f"    [{v:7}] {n}")
        print(f"              \"{d}\"")
        print(f"              {why}")
    print(f"\n    PLAIN {c['PLAIN']}   WARRANT {c['WARRANT']}   "
          f"NEITHER {c['NEITHER']}   of {len(ASSERTIONS)}")

    cp = Counter(v for _p, v in PROCEDURES)
    print("\n  The eight accounts-payable procedures:\n")
    for p, v in PROCEDURES:
        print(f"    [{v:7}] {p}")
    print(f"\n    PLAIN {cp['PLAIN']}   WARRANT {cp['WARRANT']}   "
          f"NEITHER {cp['NEITHER']}   of {len(PROCEDURES)}")

    print("\n  READ AGAINST YESTERDAY. My own list scored 3 of 8 as")
    print("  unanswerable-without-us. The profession's scores")
    print(f"  {c['WARRANT'] + cp['WARRANT']} of {len(ASSERTIONS) + len(PROCEDURES)}"
          f" — a lower rate, and the honest number. Most of what an")
    print("  auditor does all day is ordinary querying that SQL already")
    print("  does well. What we hold is a minority of the work, and it is")
    print("  the minority the whole audit exists for.")
    print("\n  AND THE ONE THAT BEATS BOTH SCHEMAS. Completeness — the")
    print("  assertion auditors rank hardest for payables — is answerable")
    print("  by no ledger whatever. The invoice nobody entered leaves no")
    print("  row to carry a warrant. Our column is silent there, and any")
    print("  pitch that forgets to say so is selling.")

    # ---------------------------------------------------------------- ISA 500
    print("\n" + "=" * 78)
    print("ISA 500'S HIERARCHY — measured as the partial order it is")
    print("=" * 78)
    grades = list(itertools.product((0, 1), repeat=4))
    pairs = list(itertools.combinations(grades, 2))
    inc = [(a, b) for a, b in pairs if not dominates(a, b)
           and not dominates(b, a)]
    print(f"\n  distinct grades the four axes give        {len(grades)}")
    print(f"  pairs of grades                           {len(pairs)}")
    print(f"  pairs that are INCOMPARABLE               {len(inc)}"
          f"  ({100*len(inc)//len(pairs)}%)")
    print("  — neither is better evidence than the other, and a ranking")
    print("    that reports a single grade has to invent an answer here.")

    strictly_below = [(a, b) for a, b in inc
                      if meet(a, b) != a and meet(a, b) != b]
    print(f"\n  incomparable pairs whose MEET is strictly below both  "
          f"{len(strictly_below)} of {len(inc)}")
    a, b = strictly_below[0]
    print(f"    e.g.  {name(a)}")
    print(f"      and {name(b)}")
    print(f"      ->  {name(meet(a, b))}")
    print("    A total built from those two is worse evidence than either")
    print("    of its parts. `honest_sum` takes the weakest part, which on")
    print("    a LADDER is the same thing and on a LATTICE is not. Our")
    print("    aggregate is therefore right by accident on a two-valued")
    print("    column and wrong the day the column gets richer.")

    ours = {(1, 1, 1, 1): "earned"}
    collapsed = len(grades) - len(ours)
    print(f"\n  what our two-valued column does to it")
    print(f"    grades that map to 'earned'               1")
    print(f"    grades that map to 'credit'               {collapsed}")
    print("    Fifteen distinguishable qualities of evidence arrive as one")
    print("    word. An external original invoice obtained directly and a")
    print("    colleague's remark over coffee are both 'credit' to us and")
    print("    are not remotely the same thing to an auditor.")

    print("\n  THE DESIGN CONSEQUENCE, and it is the day's output:")
    print("    the status column should hold a POINT IN A LATTICE, not a")
    print("    word from a list of two. The four axes are somebody else's,")
    print("    published, and already agreed by the people who would have")
    print("    to use this. It also kills the idea that a warranty is a")
    print("    number — which this corpus already proved for its own")
    print("    reasons in lean/EpochBoundary.lean, from a different")
    print("    direction entirely, and that agreement is worth something.")

    # A PREDICTION THAT FAILED, kept rather than quietly corrected. This
    # file first asserted 50 incomparable pairs, by eyeballing. The count is
    # 55: comparable ordered pairs in the Boolean lattice on four axes number
    # 3**4 - 2**4 = 65, leaving 120 - 65 = 55 incomparable. Guessing at the
    # size of one's own structure is exactly the habit this corpus was built
    # to break, and the arithmetic took ten seconds once it was written down.
    assert 3**4 - 2**4 == 65 and len(pairs) - 65 == 55
    assert c["NEITHER"] == 2 and len(inc) == 55 and collapsed == 15
    print("\nASSERTIONS PROBE GREEN — measured against a list we did not write.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
