# -*- coding: utf-8 -*-
"""
Collatz through the judge: what a TOTAL claim is worth, measured.

The judge cannot settle Collatz and is not asked to. It is asked the
question it is for: what is the claim worth today, and what would change
it. The answer is sharper than expected, and it is the machine's own, not
a sentiment about it.

At the quantifier floor ZTL is DEFAULT DENY: one unchecked cell makes
'every n reaches 1' come out **F** — not "unknown". The interesting part
is what it does NOT say alongside: 'some n fails' stays F too. The
universal is denied without a counterexample being invented; the machine
refuses the claim and refuses the phantom witness in the same breath.

So today's verdict on Collatz and a verdict after a counterexample are
the same letter, and the WARRANTY is the whole difference:

  every n <= N reaches 1     T, hereditary          — exhaustion IS a witness
  every n reaches 1          F, until-verification  — denied for want of ground
  after a counterexample     F, hereditary          — refuted, and for good

Which is exactly the reading discipline: read the warranty, not the
verdict. Enumerating further changes neither: the grade over domains with
one unchecked cell is constant, and the earned neighbour theorem lifts
nothing.

Run:  python3 dilemmas/collatz.py
"""
import math
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(_HERE))

from quantifiers import ev_fo                                # noqa: E402
from ztl import T, F, Z                                      # noqa: E402
from ztljudge import judge                                   # noqa: E402
from znumjudge import judge_sheet_claim, parse_quantities     # noqa: E402
from zverify import grade                                    # noqa: E402

N = 100_000
ALL_REACH = ("all", "x", ("P", "x"))          # every n reaches 1
SOME_FAILS = ("ex", "x", ("not", ("P", "x")))  # some n does not


# ----------------------------------------------------------- the machine
def collatz_steps(limit):
    """Steps to 1 for every n <= limit, memoised. The measurement; every
    claim below is a claim ABOUT this run, never a substitute for it."""
    steps = {1: 0}
    for n in range(2, limit + 1):
        path, m = [], n
        while m not in steps:
            path.append(m)
            m = m // 2 if m % 2 == 0 else 3 * m + 1
        base = steps[m]
        for v in reversed(path):
            base += 1
            steps[v] = base
    return steps


def fo_grade(phi, dom, cells):
    """The warranty of a first-order verdict: is it invariant under every
    way the unchecked cells could come out? (The propositional grade of
    zverify, lifted to the quantifier floor — same question, same answer
    shape: hereditary, or until-verification.)"""
    v0 = ev_fo(phi, dom, {"P": cells}, {})
    marks = [i for i, c in enumerate(cells) if c == Z]
    for bits in range(2 ** len(marks)):
        variant = list(cells)
        for j, i in enumerate(marks):
            variant[i] = T if (bits >> j) & 1 else F
        if ev_fo(phi, dom, {"P": tuple(variant)}, {}) != v0:
            return v0, "until-verification"
    return v0, "hereditary"


def sec1_the_run():
    print("-" * 72)
    print("1. THE RUN (the only thing here that is actually measured)")
    steps = collatz_steps(N)
    worst = max(range(1, N + 1), key=lambda n: steps[n])
    print(f"   every n <= {N} reaches 1;  longest: n = {worst} "
          f"in {steps[worst]} steps")
    print(f"   the famous small one: n = 27 takes {steps[27]} steps")
    assert steps[27] == 111 and worst == 77031 and steps[worst] == 350
    return steps


def sec2_the_quantifier_floor():
    print("-" * 72)
    print("2. THE QUANTIFIER FLOOR: what ZTL says about 'every n'")
    dom = [0, 1, 2]
    cases = [("all cells checked, all reach 1", (T, T, T)),
             ("one cell never checked       ", (T, T, Z)),
             ("one cell is a counterexample ", (T, T, F))]
    seen = {}
    for name, cells in cases:
        v, g = fo_grade(ALL_REACH, dom, cells)
        w, _ = fo_grade(SOME_FAILS, dom, cells)
        seen[name.strip()] = (v, g, w)
        print(f"   {name}: every n reaches 1 = {v} ({g:18}) "
              f"| some n fails = {w}")
    assert seen["all cells checked, all reach 1"] == (T, "hereditary", F)
    # the finding: DEFAULT DENY. An unchecked cell makes the universal F —
    # and the existential stays F as well, so no phantom witness is minted
    assert seen["one cell never checked"] == (F, "until-verification", F)
    assert seen["one cell is a counterexample"] == (F, "hereditary", T)
    print("   the two F's are not the same F: one flips the moment the")
    print("   cell is checked, the other never can. And the denied")
    print("   universal does NOT hand us a culprit — 'some n fails' is F")
    print("   until a witness actually arrives (cf. dilemmas: a court that")
    print("   catches a lie need not be able to catch the liar).")


def sec3_the_stage_court():
    print("-" * 72)
    print("3. THE STAGE COURT: does checking more buy anything?")
    rises, prev = 0, None
    for k in (2, 4, 8, 16, 32, 64, 128):
        dom = list(range(k))
        cells = tuple([T] * (k - 1) + [Z])       # everything checked but one
        v, g = fo_grade(ALL_REACH, dom, cells) if k <= 16 else (
            ev_fo(ALL_REACH, dom, {"P": cells}, {}), "until-verification")
        if k > 16:                                # one mark: two refinements
            alt = tuple([T] * k)
            g = ("hereditary"
                 if ev_fo(ALL_REACH, dom, {"P": alt}, {}) == v
                 else "until-verification")
        print(f"   {k - 1:>3} of {k:>3} cells checked and true: "
              f"every n reaches 1 = {v} ({g})")
        if prev is not None and (v, g) != prev:
            rises += 1
        prev = (v, g)
    print(f"   changes of verdict or grade as the checked part grows: {rises}")
    assert rises == 0
    print("   127 of 128 buys exactly what 1 of 2 buys. This is why")
    print(f"   2.95e20 checked values (Barina 2020) and our {N} sit in")
    print("   the same cell: no prefix is the domain.")
    # and the earned neighbour theorem lifts nothing either
    with_neighbour = judge("reaches_one_all & almost_all_drop",
                           {"reaches_one_all": "Z", "almost_all_drop": "T"})
    assert with_neighbour["disposition"] == "OPEN"
    assert with_neighbour["unverified"] == ["reaches_one_all"]
    print("   'almost every n drops below its start' (Terras 1976; Tao 2019")
    print("   in a sharper form) is EARNED — and the conjunction is still")
    print("   OPEN on the same weak link: a neighbour buys no ground.")


def sec4_the_heuristic():
    print("-" * 72)
    print("4. THE HEURISTIC: a measured drift over an unwitnessed ground")
    # the classic argument: from an odd m the next odd is (3m+1)/2^v, and
    # 'if v behaved like a coin' its mean would be 2, giving a factor 3/4
    # per odd step. Measure the factor itself over real trajectories.
    logs, steps_seen = 0.0, 0
    for start in range(3, 20001, 2):
        m = start
        while m != 1:
            nxt = 3 * m + 1
            while nxt % 2 == 0:
                nxt //= 2
            logs += math.log(nxt / m)
            steps_seen += 1
            m = nxt
    factor = math.exp(logs / steps_seen)
    print(f"   measured odd-to-odd factor over {steps_seen} odd steps: "
          f"{factor:.4f}   (the argument says 3/4 = 0.75)")
    assert 0.72 < factor < 0.78
    r = judge("parity_independence & measured_drift",
              {"parity_independence": "Z", "measured_drift": "T"})
    print(f"   'independence & drift' as a ground: {r['disposition']} — "
          f"verify {r['unverified']}")
    assert r["disposition"] == "OPEN"
    assert r["unverified"] == ["parity_independence"]
    print("   the drift is real and measured; the coin is not. The")
    print("   trajectory's own bits are produced by the map, and nobody")
    print("   has witnessed their independence — so the argument")
    print("   TRANSPORTS credit, it does not mint coin (E26).")


def sec5_the_numeric_floor():
    print("-" * 72)
    print("5. THE NUMERIC FLOOR: the same asymmetry, in one instance")
    steps = collatz_steps(N)
    q, marks = parse_quantities(
        f"s27={steps[27]} earned:run-{N} int, claimed=111 earned:folklore int")
    one = judge_sheet_claim("s27 == claimed", q, marks)
    print(f"   'n = 27 takes 111 steps': {one['disposition']}")
    assert one["disposition"] == "EARNED"
    worst = max(range(1, N + 1), key=lambda n: steps[n])
    q2, marks2 = parse_quantities(
        f"worst={steps[worst]} earned:run-{N} int, bound=200 earned:guess int")
    many = judge_sheet_claim("worst <= bound", q2, marks2)
    print(f"   'no n <= {N} needs more than 200 steps': "
          f"{many['disposition']} — witness n = {worst} at {steps[worst]}")
    assert many["disposition"] == "REFUTED"
    print("   a finite claim about one trajectory is earnable outright;")
    print("   one witness kills a universal; no number of them earns one")


if __name__ == "__main__":
    print("=" * 72)
    print("COLLATZ THROUGH THE JUDGE — a total claim, priced")
    print("=" * 72)
    sec1_the_run()
    sec2_the_quantifier_floor()
    sec3_the_stage_court()
    sec4_the_heuristic()
    sec5_the_numeric_floor()
    print("=" * 72)
    print("COLLATZ GREEN — the judge does not settle Collatz and never")
    print("could; it prices it. Today the claim is F — denied for want of")
    print("ground, default deny — and a counterexample would make it F")
    print("again, with the other warranty; the grade is the whole")
    print("difference, and the denial invents no culprit. The bounded")
    print("universal is EARNED because exhaustion is its witness; 127 of")
    print("128 checked cells buy exactly what 1 of 2 buys, which is why")
    print("2.95e20 values sit in the same cell as a hundred thousand; the")
    print("earned neighbour lifts nothing; and the famous heuristic rests")
    print("on an independence nobody has witnessed.")
