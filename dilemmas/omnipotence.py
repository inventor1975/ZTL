# -*- coding: utf-8 -*-
"""
The stone an omnipotent being cannot lift: two defects, two verdicts.

    Can he make a stone he cannot lift? If yes, there is something he
    cannot do — lift it. If no, there is something he cannot do — make
    it. Either way omnipotence fails.

The literature has two standard readings of the word, and the argument
lands differently in each (Aquinas: power over the logically possible;
Mavrodes 1963: the phrase "a stone too heavy for an omnipotent being to
lift" describes nothing). This stand does not adjudicate between them —
it MEASURES where the defect sits under each, and the two answers turn
out to be different statuses of our own floor, which is the finding.

  READING B — power over what is logically possible.
      The stone is specified as heavier than an unlimited capacity. The
      declaration is well formed and the demand has NO SOLUTION: the
      verdict is REFUTED, i.e. there is no such object. The question was
      never about power; it was a request for something with no instance.
      This is Mavrodes' answer, arrived at mechanically.

  READING A — power over anything at all, contradictions included.
      Now the defect moves. It is no longer the stone that is empty but
      the DESCRIPTION OF THE BEING: no consistent object satisfies it,
      and the specification has no admissible reading. The verdict is E,
      and it is charged to the definition, not to the deity.

So the paradox is not one puzzle but a fork in the reading, and the two
branches fail in different ways — one refuted, one unjudgeable. What no
machine can do is pick the branch: that is a stipulation about the word,
and it is exactly what the four centuries of argument were about.

Run:  python3 dilemmas/omnipotence.py
"""
import os
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from ztl import T, F, Z                                        # noqa: E402
from zpassport import passports                                # noqa: E402
from znumjudge import judge_sheet_claim, parse_quantities       # noqa: E402
from znumsolve import solve_claim                               # noqa: E402


def sec1_reading_b_the_stone_has_no_instance():
    print("-" * 72)
    print("1. READING B (power over the logically possible): THE STONE")
    # capacity is unbounded; the stone is asked to exceed it
    q, m = parse_quantities("stone=? credit kg, capacity=inf earned:def kg")
    r = solve_claim("stone > capacity", q, m)
    print(f"   'a stone heavier than an unlimited capacity': "
          f"{r['disposition']}")
    assert r["disposition"] == "REFUTED"
    print("   REFUTED, not E: the request is perfectly well formed and has")
    print("   no solution. There is no such stone — which is Mavrodes'")
    print("   answer, and the machine reaches it without knowing his name.")
    # and note what is NOT refuted: ordinary limits are still sayable
    q2, m2 = parse_quantities("stone=? credit kg, capacity=1000 earned:crane kg")
    r2 = solve_claim("stone > capacity", q2, m2)
    print(f"   the same demand of a crane rated 1000 kg: "
          f"{r2['disposition']}   (a heavier stone exists)")
    assert r2["disposition"] != "REFUTED"
    print("   so the impossibility is produced by the UNLIMITED capacity,")
    print("   not by the shape of the question: 'heavier than everything'")
    print("   is a request with no instance, and 'no instance' is a")
    print("   refutation rather than a limit on anybody's power.")


def sec2_reading_a_the_being_has_no_instance():
    print("-" * 72)
    print("2. READING A (power over anything at all): THE BEING")
    # the defining pair: he can do X, and he cannot do X
    # the right shape is NOT a two-cycle (that is merely undetermined —
    # measured, and it cost this file a rewrite). Under reading A the SAME
    # object must be both liftable and not: he lifts everything, and this
    # stone was made unliftable by him.
    system = {"liftable_by_him": ("not", "liftable_by_him")}
    reports = {tuple(sorted(c)): (k, w) for c, k, w in passports(system)[1]}
    for comp, (kind, why) in sorted(reports.items()):
        print(f"   {'/'.join(comp):28}: {kind} — {why}")
    assert any(k == "PARADOX" for k, _ in reports.values())
    # and the same emptiness on the numeric floor: a capacity that must be
    # both unlimited and exceeded has no admissible value
    q, m = parse_quantities("capacity=[inf,0] credit kg")
    r = judge_sheet_claim("capacity >= 0", q, m)
    print(f"   'a capacity both unlimited and exceeded': "
          f"{r['disposition']} — {r['why']}")
    assert r["disposition"] == "E"
    print("   E, and charged to the DEFINITION: under this reading nothing")
    print("   consistent answers to the word, so the term has no reading —")
    print("   not a deity that fails a test, a specification that never")
    print("   named anything.")


def sec3_what_classical_logic_does_here():
    print("-" * 72)
    print("3. AND WHY THE ARGUMENT COULD RUN SO LONG")
    print("   Under reading A the premises are inconsistent, and classical")
    print("   logic entails EVERYTHING from them — including that the being")
    print("   exists and that it does not. An engine returns `unsat` and")
    print("   stops; a disputant reaches for whichever consequence suits.")
    print("   Here the contradictory pair is quarantined (§2, refusal")
    print("   permanent) and the rest of the sheet keeps its verdicts —")
    print("   which is why the two readings can be compared at all instead")
    print("   of one of them swallowing the table.")
    print()
    print("   The fork itself is not decidable by any machine: which sense")
    print("   of 'omnipotent' is meant is a stipulation about a word. What")
    print("   the machine adds is that the two branches fail DIFFERENTLY —")
    print("   REFUTED for the stone, E for the being — so the disputants")
    print("   were not disagreeing about a fact but about which of two")
    print("   defects they were looking at.")


if __name__ == "__main__":
    print("=" * 72)
    print("OMNIPOTENCE AND THE STONE — two defects, two verdicts")
    print("=" * 72)
    sec1_reading_b_the_stone_has_no_instance()
    sec2_reading_a_the_being_has_no_instance()
    sec3_what_classical_logic_does_here()
    print("=" * 72)
    print("OMNIPOTENCE GREEN — the puzzle is a fork in a word, and the two")
    print("branches break in different places. Read omnipotence as power")
    print("over the possible and the STONE is refuted: a request with no")
    print("instance, no limit on anyone's power. Read it as power over")
    print("anything at all and the BEING is unjudgeable: E, charged to the")
    print("definition, since nothing consistent answers to the term. No")
    print("machine picks the branch — that is a stipulation about a word,")
    print("and it is what the argument was always about.")
