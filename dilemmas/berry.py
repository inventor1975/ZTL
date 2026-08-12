# -*- coding: utf-8 -*-
"""
Berry's paradox: a description that is fine until it is added to the book.

    "The least natural number not nameable in fewer than twenty
    syllables" — and that phrase names it in nineteen.

The docket lists Berry among the cases its passport cannot judge, on the
grounds that definability needs arithmetized naming, which a finite
language does not express. That is right about the passport and wrong as
a verdict on the case: the paradox does not need arithmetic. It needs a
NAMING SYSTEM that changes when a description is added to it, and that is
finite, computable, and measurable here.

The model: a small universe of numbers, a naming system that gives each
one its cost in syllables, and the Berry description, which picks the
cheapest number no cheap name reaches. Everything is decidable while the
book of names is FIXED.

MEASURED HERE:

  1. at a fixed stage the description is perfectly well behaved: it names
     one number, the verdict is EARNED, and nothing is paradoxical;
  2. add the phrase itself to the book — it is, after all, a name, and a
     short one — and the description denotes a different number. Iterate:
     the answer marches (100 -> 107 -> 170 -> 177 in the measured toy) and
     never repeats, because each stage makes the current answer cheap and
     the next must lie further on. In a finite universe the march ends in
     E: every number now has a cheap name, and "the least one without"
     picks out nothing at all;
  3. so the defect is not in the description and not in the number. It is
     the use of a description ACROSS the stage its own addition creates —
     the Epoch Boundary of §§21-23, met from a new direction.

The ending is worth pausing on, since it was not planned: Berry's
iteration terminates in the fourth corner of the reading set, the same E
that the impossible clause and the incomparable units produce. A
description can be emptied by having its subject matter named out from
under it.

That reading also explains the standard cure without inventing one:
forbid the phrase from naming (a hierarchy of languages) and stage 1
never happens; allow it and there is no stage at which the answer holds.
Both are decisions about the book of names, not discoveries about
numbers.

Run:  python3 dilemmas/berry.py
"""
import os
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from ztl import T, F, Z                                        # noqa: E402
from ztljudge import judge                                     # noqa: E402

UNIVERSE = range(0, 200)
BUDGET = 5                       # "fewer than five syllables", scaled down
PHRASE_COST = 4                  # and the Berry phrase itself costs four


DIGIT = [2, 1, 1, 1, 1, 1, 1, 2, 1, 1]             # zero, one, two, ... nine


def base_cost(n):
    """A toy naming system: read the decimal digits aloud and count the
    syllables. Nothing below depends on the exact table — only on its
    being FIXED while a stage lasts."""
    return sum(DIGIT[int(d)] for d in str(n))


def berry(cost):
    """The least number no name in the book reaches under the budget."""
    for n in UNIVERSE:
        if cost(n) >= BUDGET:
            return n
    return None


def sec1_a_fixed_book_is_well_behaved():
    print("-" * 72)
    print("1. WITH THE BOOK OF NAMES FIXED, NOTHING IS PARADOXICAL")
    n0 = berry(base_cost)
    cheap = [n for n in UNIVERSE if base_cost(n) < BUDGET]
    print(f"   budget: fewer than {BUDGET} syllables")
    print(f"   numbers reachable under it: {len(cheap)} of {len(UNIVERSE)}")
    print(f"   the least number NOT reachable: {n0}  "
          f"(costs {base_cost(n0)})")
    r = judge("berry_denotes_n0", {"berry_denotes_n0": T})
    print(f"   'the description denotes {n0}': {r['disposition']}")
    assert n0 is not None and r["disposition"] == "EARNED"
    print("   a decidable question with an answer. The description is not")
    print("   suspicious, self-referential or ill-formed — at this stage.")
    return n0


def sec2_add_the_phrase_and_watch(n0):
    print("-" * 72)
    print("2. NOW ADD THE PHRASE TO THE BOOK — IT IS A NAME, AND A SHORT ONE")
    cost = {n: base_cost(n) for n in UNIVERSE}
    target, seq, repeated = n0, [n0], False
    while True:
        cost[target] = min(cost[target], PHRASE_COST)   # the phrase names it
        nxt = berry(lambda n: cost[n])
        if nxt is None:
            break
        if nxt in seq:
            repeated = True
            break
        seq.append(nxt)
        target = nxt
    print(f"   the description's answer, stage by stage: "
          f"{' -> '.join(str(x) for x in seq[:12])}"
          f"{' ...' if len(seq) > 12 else ''}")
    print(f"   stages before the answer stopped moving: {len(seq)}")
    print(f"   did it ever repeat an answer? {repeated}")
    print(f"   and how it ended: {'E — no number left unnamed' if not repeated else 'a cycle'}")
    assert not repeated and nxt is None
    print("   It never settles and never repeats: each stage names the")
    print("   current answer cheaply, so the next answer must be a further")
    print("   number, and the march runs to the end of the universe. There")
    print("   the description denotes NOTHING — the empty reading set, the")
    print("   status this corpus calls E — because every number now has a")
    print("   cheap name and 'the least one without' picks out no object.")
    return len(seq)


def sec3_the_reading():
    print("-" * 72)
    print("3. WHAT THE MACHINE IS ACTUALLY SAYING")
    print("   The description is decidable at every stage and denotes a")
    print("   different number at each one. There is no stage at which the")
    print("   answer holds, and no contradiction inside any stage — which")
    print("   is exactly the shape of an EPOCH crossing (§§21-23): a claim")
    print("   used in the epoch that its own registration creates.")
    print("   Neither the number nor the phrase is defective. What fails is")
    print("   the assumption that the book of names can contain a")
    print("   description that quantifies over the book of names.")
    # the two standard cures, as what they are: decisions about the book
    print()
    print("   The two classical cures are decisions, not discoveries:")
    print("     * bar the phrase from naming (a hierarchy of languages) —")
    print("       stage 1 never happens and stage 0's answer stands;")
    print("     * allow it — and no stage's answer stands.")
    print("   The corpus has a name for a choice like that: a stipulation,")
    print("   admissible, declarable, and to be written down rather than")
    print("   discovered. What it is NOT is a fact about numbers.")


if __name__ == "__main__":
    print("=" * 72)
    print("BERRY — the description that changes the book it is written in")
    print("=" * 72)
    n0 = sec1_a_fixed_book_is_well_behaved()
    period = sec2_add_the_phrase_and_watch(n0)
    sec3_the_reading()
    print("=" * 72)
    print("BERRY GREEN — with the book of names fixed the description is")
    print("decidable and its answer is EARNED; add the phrase to the book")
    print("and the answer moves at every stage and never settles. The")
    print("defect is neither in the number nor in the phrase but in using a")
    print("description across the stage its own addition creates — the")
    print("epoch boundary, reached from definability instead of from time.")
    print("The classical cures are decisions about the book, and the corpus")
    print("calls such a thing a stipulation.")
