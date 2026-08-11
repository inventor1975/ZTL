# -*- coding: utf-8 -*-
"""
The heap, judged: where the sorites keeps its sting.

Not a self-referential case — a different family from the docket's
twenty-four. A strip of numbers, two witnessed ends (10000 grains is a
heap; 0 grains is not), an unwitnessed middle, and one seductive premise:

    tolerance:  for every n,  heap(n) -> heap(n-1)      "one grain never decides"

The classical argument chains tolerance ten thousand times and lands on
"0 grains is a heap". Every step is modus ponens, and ZTL KEEPS modus
ponens (measured: alive, and stronger than in LP) — so the resolution
cannot be "the logic broke". It has to be the price of the premise.

MEASURED HERE, and the last one is the finding:

  1. every tolerance instance touching the unwitnessed middle is F —
     Z -> Z is F, the fallen law of free truth in its everyday costume;
  2. the tolerance premise as a whole is F HEREDITARILY, and refuted by
     the two witnessed ends ALONE: however the middle is filled in, a
     strip that starts F and ends T must jump somewhere;
  3. and yet "there is a sharp grain" stays F while the middle is
     unwitnessed — even though "some step fails" is T. The machine
     refuses tolerance AND refuses to name a cutoff it cannot witness.

Which locates the sting exactly, and NOT where this file first guessed:
the quantifier De Morgan holds here (~forall and "some step fails" agree).
The break is one step further in — classical logic rewrites a failed
implication ~(p -> q) as a cliff p & ~q, and those two part company at a
mark: ~(Z -> Z) is T while Z & ~Z is F. A step can fail because NEITHER
neighbour has been witnessed, which is exactly the situation in the
middle of the strip. The epistemicist's hidden cutoff is bought with that
identification, and nobody paid for it.

The cure the machine names is the one people actually use: stipulate.
A stipulated threshold is UNDERDETERMINED before the act and grounded
after it — the boundary is real, and it is ours. Section 5 rides that on
the everyday instance: "a large sum" in an estimate, which is a sorites
with money in it.

Run:  python3 dilemmas/solved/sorites/sorites.py
"""
import os
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.dirname(os.path.abspath(__file__)))))
sys.path.insert(0, _ROOT)

from ztl import T, F, Z, AND, IMP, NOT                       # noqa: E402
from znumjudge import judge_sheet_claim, parse_quantities    # noqa: E402
from zpassport import passports                              # noqa: E402

K = 10_000            # grains in the witnessed heap
HEAP_FLOOR = 9_000    # at or above this, someone has pointed and said "heap"
SAND_CEIL = 10        # at or below this, everyone agrees it is not a heap


def strip(murk=Z, cut=None):
    """heap(n) for n = 0..K. The ends are witnessed; the middle is either
    unwitnessed (murk=Z) or settled by a stipulated cut."""
    out = []
    for n in range(K + 1):
        if n >= HEAP_FLOOR:
            out.append(T)
        elif n <= SAND_CEIL:
            out.append(F)
        elif cut is not None:
            out.append(T if n >= cut else F)
        else:
            out.append(murk)
    return out


def tolerance_instances(h):
    """heap(n) -> heap(n-1), for every n."""
    return [IMP(h[n], h[n - 1]) for n in range(1, len(h))]


def forall(vals):
    """The greedy universal: T only if every cell is T (§: no free truth)."""
    return T if all(v == T for v in vals) else F


def exists(vals):
    return T if any(v == T for v in vals) else F


def sec1_the_instances():
    print("-" * 72)
    print("1. THE PREMISE, INSTANCE BY INSTANCE")
    h = strip()
    inst = tolerance_instances(h)
    earned = sum(1 for v in inst if v == T)
    denied = sum(1 for v in inst if v == F)
    print(f"   {len(inst)} instances of 'heap(n) -> heap(n-1)':  "
          f"T = {earned},  F = {denied}")
    print(f"   inside the witnessed heap (n = {K}):        "
          f"{IMP(h[K], h[K - 1])}")
    print(f"   stepping from witnessed heap into the murk: "
          f"{IMP(h[HEAP_FLOOR], h[HEAP_FLOOR - 1])}")
    print(f"   deep in the murk (n = 5000):                "
          f"{IMP(h[5000], h[4999])}")
    print(f"   stepping from the murk into witnessed sand: "
          f"{IMP(h[SAND_CEIL + 1], h[SAND_CEIL])}")
    assert IMP(Z, Z) == F and IMP(T, Z) == F and IMP(Z, F) == F
    # exactly the murky band and its two shoulders are denied
    assert denied == (HEAP_FLOOR - SAND_CEIL)
    print("   Z -> Z is F: in the murk the premise is not 'unknown', it is")
    print("   DENIED — 'one grain never decides' is free truth, and free")
    print("   truth is what this logic refuses to hand out (p -> p falls")
    print("   at a mark for the same reason).")


def sec2_the_premise_whole():
    print("-" * 72)
    print("2. THE PREMISE AS A WHOLE, AND ITS WARRANTY")
    tol_open = forall(tolerance_instances(strip()))
    print(f"   tolerance over the whole strip, middle unwitnessed: {tol_open}")
    # every way of filling the middle in — not just the two extremes:
    # a strip that is F at 0 and T at K must jump, so SOME instance is F
    worst = []
    for cut in (SAND_CEIL + 1, 100, 4711, HEAP_FLOOR):
        worst.append(forall(tolerance_instances(strip(cut=cut))))
    for murk in (T, F):
        worst.append(forall(tolerance_instances(strip(murk=murk))))
    print(f"   under every refinement tried ({len(worst)}): "
          f"{sorted(set(worst))} — never T")
    assert set(worst) == {F} and tol_open == F
    print("   so tolerance is F HEREDITARILY, and the two witnessed ends")
    print("   alone refute it: a strip that begins F and ends T must jump.")
    print("   Note what this is NOT: not a trick of the third value. This")
    print("   half of the argument is the classical one, and it stands.")


def sec3_the_sting():
    print("-" * 72)
    print("3. WHERE THE STING IS: the step nobody paid for")
    h = strip()
    tol = forall(tolerance_instances(h))
    not_tol = NOT(tol)
    # three readings of "tolerance fails", which classical logic treats as
    # one and the same. Measured, they are not.
    some_step_fails = exists([NOT(v) for v in tolerance_instances(h)])
    sharp = exists([AND(h[n], NOT(h[n - 1])) for n in range(1, len(h))])
    print(f"   tolerance                        = {tol}")
    print(f"   ~tolerance                       = {not_tol}")
    print(f"   'some step fails'  (exists ~inst) = {some_step_fails}")
    print(f"   'some grain is a cliff' (H & ~H-) = {sharp}")
    assert tol == F and not_tol == T
    assert some_step_fails == T          # the quantifier De Morgan HOLDS here
    assert sharp == F                    # and yet no cliff is asserted
    print("   so the quantifier De Morgan is NOT the culprit — it holds:")
    print("   ~forall and 'some step fails' agree, both T. The break is one")
    print("   step further in, where classical logic rewrites a failed")
    print("   implication as a cliff:")
    for p, q in ((T, Z), (Z, Z), (Z, F)):
        print(f"     p={p} q={q}:  ~(p -> q) = {NOT(IMP(p, q))}   "
              f"but  p & ~q = {AND(p, NOT(q))}")
    assert all(NOT(IMP(p, q)) != AND(p, NOT(q)) for p, q in
               ((T, Z), (Z, Z), (Z, F)))
    print("   THAT is the sorites' sting: 'the step from n to n-1 does not")
    print("   hold' is earned, and 'n is a heap and n-1 is not' is not the")
    print("   same sentence. A step can fail because neither neighbour has")
    print("   been witnessed — which is the actual situation in the middle")
    print("   of the strip. Classical logic identifies the two and hands")
    print("   you a hidden sharp grain; that identification is the unpaid")
    print("   bill. (Honest reading of the F: this logic asserts only what")
    print("   is witnessed, so 'no cliff' means 'no cliff shown' — default")
    print("   deny, the same move it makes on any unwitnessed claim.)")
    # and once the middle IS settled, the boundary appears — exactly one
    h2 = strip(cut=4711)
    sharp2 = [n for n in range(1, len(h2)) if AND(h2[n], NOT(h2[n - 1])) == T]
    print(f"   after a stipulated cut at 4711: sharp grains = {sharp2}")
    assert sharp2 == [4711]
    print("   one boundary, exactly where we put it. Not discovered — set.")


def sec4_the_cure():
    print("-" * 72)
    print("4. THE CURE THE MACHINE NAMES: an act, not a discovery")
    h = strip()
    murky = [n for n in range(K + 1) if h[n] == Z]
    print(f"   unwitnessed cells: {len(murky)} "
          f"({murky[0]}..{murky[-1]}) — each free to be settled either way")
    print("   settling one of them is not a measurement of sand; nothing in")
    print("   the world distinguishes 4710 grains from 4711. It is a")
    print("   STIPULATION: two solutions, we pick one. Where there is no")
    print("   ground there is no target — and that is where our freedom is")
    print("   (the capstone the foreknowledge dilemma earned from the other")
    print("   side). The paradox is not a disease of vagueness; it is the")
    print("   bill for a boundary nobody agreed to draw.")


def sec5_the_everyday_sorites():
    print("-" * 72)
    print("5. THE SAME THING WITH MONEY IN IT (where it actually bites)")
    # 'a large sum' with no norm behind it: the threshold is a bare number
    q, m = parse_quantities("amount=150000 earned:invoice-88 RUB, "
                            "threshold=100000 credit RUB")
    loose = judge_sheet_claim("amount >= threshold", q, m)
    print(f"   'the sum is large' (threshold nobody set): "
          f"{loose['disposition']} — cure {loose['next_check']}")
    assert loose["disposition"] == "ON CREDIT"
    assert loose["next_check"] == ["document threshold"]
    # the same claim once a shared norm sets the cut
    q2, m2 = parse_quantities("amount=150000 earned:invoice-88 RUB, "
                              "threshold=100000 earned:reg-44-p3 RUB")
    tight = judge_sheet_claim("amount >= threshold", q2, m2)
    print(f"   the same sum against a cited norm: {tight['disposition']}")
    assert tight["disposition"] == "EARNED"
    print("   so the everyday sorites — 'a large sum', 'a material")
    print("   deviation', 'an overdue payment' — is cured the way the")
    print("   heap is: by citing the act that drew the line. And the")
    print("   yardstick has to be a SHARED one; a private threshold reads")
    print("   the judge's own wish (the retribution capstone, measured).")


def sec6_is_it_even_a_paradox():
    print("-" * 72)
    print("6. THE PASSPORT: is the heap a paradox at all?")
    # the classifier that types the docket's twenty-four, run on a strip of
    # the heap with the liar standing next to it for scale
    system = {"h5": Z, "h6": Z, "h7": Z,
              "tol6": ("imp", "h6", "h5"), "tol7": ("imp", "h7", "h6"),
              "liar": ("not", "liar")}
    out = passports(system)
    kinds = {tuple(sorted(comp)): (kind, why) for comp, kind, why in out[1]}
    for comp in (("liar",), ("h5",), ("tol6",)):
        kind, why = kinds[comp]
        print(f"   {comp[0]:6}: {kind:12} — {why}")
    assert kinds[("liar",)][0] == "PARADOX"
    assert kinds[("h5",)][0] == "INPUT"
    assert kinds[("tol6",)][0] == "DOWNSTREAM"
    assert "conditional" in kinds[("tol6",)][1]      # curable, unlike the liar
    assert "PERMANENT" in kinds[("liar",)][1]
    print("   so by our own classifier THE HEAP IS NOT A PARADOX. The liar")
    print("   has no classical model and no act ever lifts him; a heap cell")
    print("   has two models and is lifted the moment somebody decides. The")
    print("   tolerance premise is not even ill in itself — it is")
    print("   DOWNSTREAM, infected by neighbours the passport names.")
    print("   (Register note: the passport reads Z in the LAZY register —")
    print("   'not computed yet', it classifies the refusal; the verdict")
    print("   above reads the GREEDY one — 'truth is not taken on credit',")
    print("   it decides whether to sign. Two questions, two answers, and")
    print("   both are ours.)")


if __name__ == "__main__":
    print("=" * 72)
    print("THE HEAP, JUDGED — a sorites with its price list")
    print("=" * 72)
    sec1_the_instances()
    sec2_the_premise_whole()
    sec3_the_sting()
    sec4_the_cure()
    sec5_the_everyday_sorites()
    sec6_is_it_even_a_paradox()
    print("=" * 72)
    print("SORITES GREEN — tolerance is refuted, hereditarily, by the two")
    print("witnessed ends alone; every instance touching the unwitnessed")
    print("middle is denied outright, because Z -> Z is F and 'one grain")
    print("never decides' is free truth. And still no sharp grain is")
    print("asserted: 'some step fails' is T while 'some grain is a cliff'")
    print("is F, so the unpaid step is the identification ~(p -> q) = p & ~q")
    print("— a step can fail for want of a witness on BOTH sides. The")
    print("boundary arrives only with the act that draws it: stipulated,")
    print("shared, and citable.")
