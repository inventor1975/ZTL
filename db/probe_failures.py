# -*- coding: utf-8 -*-
"""
The measurement week, day five: against real audits that actually failed.

The obvious next test was to find a working auditor and ask whether our eight
questions match their day. The curator declined it, on two grounds and both
right: dragging a professional into an unpaid trial for our benefit is not
decent, and a polite stranger cannot refute us — they nod.

Documented failures can. These are cases where the profession itself
concluded, on the record, that an audit did not work, and said what went
wrong. So the question here is not "would an auditor like this" but the one
that can come back NO: given each documented failure mode, what would this
instrument actually have done.

Three verdicts, and the middle one is where honesty lives:

    TOUCHES     the machinery addresses this failure mode directly
    EXPOSES     it would not have caught it, but the shape of the reliance
                would have been visible in the report instead of hidden
    OUT         nothing here reaches it, at any effort

Sources are named per row. Nothing below is a claim about what any firm
should have done; they are public findings, used as a test set.

Run:  python3 db/probe_failures.py
"""
import sys
from collections import Counter

# (what failed, source, verdict, the honest reasoning)
CASES = [
    ("Wirecard: €1.9bn of assets evidenced by FORGED bank letters",
     "Wirecard insolvency 2020, widely reported",
     "OUT",
     "The one everybody will ask about, so it goes first and the answer is "
     "no. A ground is an opaque name here; the machine never looks inside "
     "one. It would have recorded `cash rests on bank-letter-X`, found the "
     "ground present, and printed a clean EARNED. A forgery is invisible to "
     "this instrument BY CONSTRUCTION — it is the published ceiling, not an "
     "oversight. Anyone selling this as fraud detection is selling."),

    ("Wirecard: the confirmation was never obtained from the bank directly, "
     "for more than three years",
     "reported as a routine procedure not performed",
     "EXPOSES",
     "Different shape, and this one we hold. 'Obtained directly by the "
     "auditor' is one of ISA 500's four axes, measured in probe_lattice. A "
     "figure carrying that axis and a figure lacking it are different "
     "grades, and a report that prints €1bn at the lower grade is not the "
     "same document as one printing a clean number. Not detection — "
     "exposure. It makes the gap a visible property rather than an absence "
     "nobody has to notice."),

    ("Carillion: going concern sustained on optimistic contract revenue",
     "FRC investigation of the 2018 collapse",
     "EXPOSES",
     "An estimate and a measurement are both numbers in a column, and only "
     "the warrant separates them — the 'accuracy, valuation and allocation' "
     "assertion, marked WARRANT in probe_assertions. The judgement of "
     "whether the estimate is reasonable stays entirely with the auditor. "
     "What changes is that a conclusion resting on it cannot print as "
     "though it rested on a measurement."),

    ("PCAOB, the recurring finding: insufficient testing of the DATA AND "
     "REPORTS used to support audit conclusions",
     "PCAOB inspection reports; ~40% of audits inspected carried "
     "Part I.A deficiencies in 2022, ~39% in 2024",
     "TOUCHES",
     "The closest fit in the whole set, and it is the profession's single "
     "most repeated finding rather than a spectacular one-off. A conclusion "
     "resting on data whose own warrant was never established is exactly "
     "what the ledger computes: the chain is explicit, and a conclusion "
     "standing on an ungrounded input comes back ON CREDIT rather than "
     "EARNED, by arithmetic and without anyone noticing to check."),

    ("PCAOB: reliance on internal controls without evidence justifying the "
     "decision to rely",
     "PCAOB inspection reports, internal control testing",
     "TOUCHES",
     "A ground about a ground, which is the case the cascade was built for. "
     "If the controls claim is itself ungrounded, everything downstream "
     "inherits that and says so. This is the same computation as the forged "
     "invoice, run one level up."),

    ("Completeness: liabilities that were never recorded at all",
     "ISA 315 assertion, ranked hardest for payables",
     "OUT",
     "Already settled on day two and repeated here because it is the one "
     "an auditor cares most about. The invoice nobody entered leaves no row "
     "to carry a warrant. No ledger reaches it, ours included."),

    ("Fee-driven auditor dependence on the client",
     "recurring in the comparative literature on Wirecard, Carillion, FTX",
     "OUT",
     "Economic and social. Nothing in a calculus touches who pays whom."),

    ("Weak whistleblower protection; regulatory inertia; jurisdictional gaps",
     "same comparative literature",
     "OUT",
     "Institutional. Named here so the list is not quietly filtered to the "
     "cases we win."),
]


def main():
    print("=" * 78)
    print("AGAINST AUDITS THAT ACTUALLY FAILED")
    print("=" * 78)
    for what, src, verdict, why in CASES:
        print(f"\n  [{verdict:7}] {what}")
        print(f"            source: {src}")
        print(f"            {why}")

    c = Counter(v for _w, _s, v, _y in CASES)
    print("\n" + "=" * 78)
    for k in ("TOUCHES", "EXPOSES", "OUT"):
        print(f"  {k:9} {c[k]} of {len(CASES)}")

    print("""
  THE HEADLINE, and it is deflating on purpose.

  NOT ONE of these is PREVENTED. This instrument does not catch liars.
  It has no opinion about whether a document is genuine, whether an
  estimate is reasonable, or whether anyone should have looked harder.
  Every ground is a name it takes on trust, which is written down as a
  ceiling and is now confirmed against the most famous audit failure of
  the decade: Wirecard would have printed EARNED, cleanly, for years.

  What the count does say is narrower and still worth something. The two
  it TOUCHES are not the dramatic cases — they are the PCAOB's most
  repeated finding, present in something like four audits in ten. A
  conclusion resting on data whose own warrant was never established is
  an arithmetic fact once the chain is written down, and it is currently
  found by a human being noticing.

  And the two it EXPOSES are the honest middle: the reliance becomes a
  visible property of the report rather than an absence that has to be
  spotted. That is worth less than detection and more than nothing, and
  conflating it with detection is the exact trade this corpus refuses.

  WHAT THIS DOES NOT MEASURE. Whether anybody wants it. Five days have
  measured the instrument against standards, against failures, against
  SQL — and not once against a person who would have to type the links
  in. That remains the open question and no probe can close it.""")
    assert c["OUT"] >= 4 and c["TOUCHES"] >= 2
    print("\nFAILURES PROBE GREEN — scored against cases that could refuse us.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
