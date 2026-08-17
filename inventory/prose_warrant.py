# -*- coding: utf-8 -*-
"""
The corpus's own prose, put through the corpus's own judge.

THE OBSERVATION THAT PRODUCED THIS FILE, and it was the curator's. On
2026-08-17 four defects were found in a note hours before deposit, and none of
them was a wrong number: every figure any program printed was correct. All four
lived in SENTENCES ABOUT the numbers. His question was the right one — how can
a machine-checked core carry stands that lie? — and the answer is that nothing
checked that layer. Lean checks the calculus; `note_claims.py` checks digits
against program output and says so in its own §5: *a note whose figures are
right and whose claims are wrong passes here*.

His second observation is what makes this file possible: **ZTL already takes
prose apart.** `dilemmas/cogito.py` does it to Descartes. Split the sentence
into atoms, mark which atoms the act itself witnesses, and the judge reports
whether the conclusion is EARNED or merely ON CREDIT, naming the weak link.
`cogito ergo sum` comes out OPEN on the atom `i` — the owner, whom the act of
thinking never delivers — while his own emendation *Sensus est, ergo est* comes
out EARNED with no weak link at all, because there every atom is witnessed by
the one act.

**Today's four failures have exactly that shape.** Each was a leap from what a
run witnessed to a universal it did not:

    cogito:  an occurrence of thinking  ->  an OWNER of it       (atom `i`)
    ours:    one table of one edge kind ->  EVERY kind of edge   (atom `k`)
    ours:    one seed                   ->  EVERY seed           (atom `u`)
    ours:    one host's package graph   ->  a property of graphs (atom `h`)
    ours:    one commit's edit          ->  every file it named  (atom `f`)

So the sentences are judged here the same way the cogito is, and the corrected
wording is judged beside each. A correction that does not turn OPEN into EARNED
is not a correction, it is a rephrasing — and this file is where that gets
tested rather than felt.

WHAT THIS DOES NOT DO. It does not read prose. The split into atoms is done by
hand, by the author, exactly as in the cogito stand — and a dishonest split
gives a dishonest verdict, which is a ceiling this file cannot raise. What it
buys is that the split is written down, public, and re-run: an argument about
whether a sentence over-claims becomes an argument about its atoms.

Run:  python3 inventory/prose_warrant.py
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ztljudge import judge                                     # noqa: E402

# Each case: the sentence as it stood, its atoms, what the run actually
# witnessed (marked T), and the corrected sentence with its own atoms.
#
#   claim     the formula whose warrant is at issue
#   witness   atoms the run genuinely delivered
#   gap       the atom the sentence needed and no run supplied
CASES = [
    dict(
        name="probe_blindspot, the direction of the incompleteness error",
        broke='"There is no symmetric case where an incomplete map '
              'flatters the danger instead of hiding it."',
        claim="(shared_positive & all_kinds_checked) -> one_directional",
        witness={"shared_positive": "T"},
        gap="all_kinds_checked",
        gloss="the shared-origin table was run; the enumeration of edge KINDS "
              "never was — and the alternatives table, thirty lines below, is "
              "the case declared impossible",
        fixed='"Within this table, and for this kind of edge, the error is '
              'never negative."',
        fixed_claim="shared_positive",
    ),
    dict(
        name="probe_criterion, the r*/q* crossings",
        broke='"The two crossings coincide at the sweep\'s own step of 0.05."',
        claim="(coincide_at_shipped_seed & holds_for_all_seeds) -> "
              "property_of_the_step",
        witness={"coincide_at_shipped_seed": "T"},
        gap="holds_for_all_seeds",
        gloss="one seed was run; the sentence spoke about the grid. Measured "
              "afterwards: 2 of 7 seeds",
        fixed='"On the shipped seed the crossings land in the same cell of '
              'the 0.05 grid; across seven seeds that holds on two."',
        fixed_claim="coincide_at_shipped_seed",
    ),
    dict(
        name="warrant note §3.8, the host's package graph",
        broke='"2,444 packages ... A_crit = 0.868" quoted as the figure.',
        claim="(measured_on_this_host & host_is_stable) -> stated_figure",
        witness={"measured_on_this_host": "T"},
        gap="host_is_stable",
        gloss="installing PostgreSQL moved every one of them within the hour",
        fixed='"Some two and a half thousand packages; the exact figures are '
              'printed by db/probe_real.py."',
        fixed_claim="measured_on_this_host",
    ),
    dict(
        name="commit a65804e, the Debian withdrawal",
        broke='"THE DEBIAN ANALOGY IS WITHDRAWN, in the probe and in both '
              'notes."',
        claim="(withdrawn_in_probe & withdrawn_in_every_named_file) -> "
              "withdrawal_complete",
        witness={"withdrawn_in_probe": "T"},
        gap="withdrawn_in_every_named_file",
        gloss="the commit touched five lines of a table caption in the second "
              "note and left the paragraph standing verbatim",
        fixed='"Withdrawn in the probe; the notes are checked by '
              'inventory/withdrawn_claims.py."',
        fixed_claim="withdrawn_in_probe",
    ),
]


def line(label, r):
    weak = ", ".join(r["unverified"]) or "—"
    print(f"     {label:34} {r['disposition']:<10} {r['grade']:<19} "
          f"weak=[{weak}]")
    return r


def main():
    print("=" * 78)
    print("PROSE WARRANT — the corpus's sentences through the corpus's judge")
    print("=" * 78)
    print("\n  Every figure printed by a program on 2026-08-17 was correct.")
    print("  Every defect found that day was in a SENTENCE about a figure.")
    print("  `dilemmas/cogito.py` already judges prose this way: cogito ergo")
    print("  sum is OPEN on the atom `i`, the owner the act never delivers.")
    print("  The four sentences below leap the same way — from what a run")
    print("  witnessed to a universal it did not.\n")

    open_before = earned_after = 0
    for c in CASES:
        print(f"  {c['name']}")
        print(f"    as written: {c['broke']}")
        before = judge(c["claim"], dict(c["witness"]))
        line("as written", before)
        print(f"       the unwitnessed atom: `{c['gap']}` — {c['gloss']}")
        print(f"    corrected:  {c['fixed']}")
        after = judge(c["fixed_claim"], dict(c["witness"]))
        line("corrected", after)
        print()
        # The sentence as written must ride an unverified atom, and the
        # correction must not. That is the whole test, and it is the test the
        # author could not apply to himself by reading.
        assert c["gap"] in before["unverified"], (
            f"{c['name']}: the broken sentence does not ride `{c['gap']}` — "
            "the atom split is wrong")
        assert c["gap"] not in after["unverified"], (
            f"{c['name']}: the correction still rides `{c['gap']}`")
        # AND IT MUST LAND EARNED. The first version of this file wrote each
        # correction as `witnessed -> something_new`, which the judge rightly
        # graded ON CREDIT: an implication to a fresh atom promises again what
        # no run delivered. Every case failed this file's own stated test —
        # "a correction that does not turn OPEN into EARNED is a rephrasing" —
        # and the file was shipped only after the assert was added and the
        # formulas rewritten to assert exactly what was witnessed.
        assert after["disposition"] == "EARNED", (
            f"{c['name']}: the correction is a rephrasing, not a repair — "
            f"it grades {after['disposition']}")
        open_before += before["disposition"] != "EARNED"
        earned_after += after["disposition"] == "EARNED"

    print(f"  sentences as written, riding an unpaid atom : {open_before} of "
          f"{len(CASES)}")
    print(f"  corrections that drop that atom             : {earned_after} of "
          f"{len(CASES)}")

    print("""
  WHAT THIS SETTLES, and it is smaller than it looks. It does not read
  prose: the split into atoms is the author's, by hand, exactly as in the
  cogito stand, and a self-serving split gives a self-serving verdict.
  What it changes is where the argument happens. "Is this sentence
  over-claiming?" is a matter of taste and was decided by re-reading, which
  failed four times in one day. "Does this sentence rest on an atom no run
  delivered?" is a question with an answer, written down and re-run.

  AND THE PATTERN IS ONE PATTERN. All four gaps are the same move: a
  universal quantifier nobody paid for — every kind of edge, every seed,
  every host, every file the commit named. The cogito's `i` is that move
  too: from an occurrence to its owner. The curator's emendation fixes
  Descartes by dropping the owner; the corrections above fix these
  sentences by dropping the universal. It is the same repair.""")
    print("\nPROSE WARRANT GREEN — 4 sentences, 4 unpaid atoms named, "
          "4 corrections that pay them off.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
