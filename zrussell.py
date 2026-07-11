# -*- coding: utf-8 -*-
"""
Expedition E11: Russell's paradox on ZTL-sets.

Russell is the liar dressed in membership: R = {x : x ∉ x} ⇒ R∈R ⟺
¬(R∈R). We model a universe of sets as a SYSTEM OF MEMBERSHIP FACTS
(the same instruments as for the liar: fixedpoint.py). The universe:
    a = ∅        (contains no one)
    b = {b}      (contains itself — a lawful eccentric)
    R = {x : x ∉ x}   (Russell)
    S = {x : x ∈ x}   (the truth-teller twin)
Facts: x∈y for all pairs; the definitions of Russell/the twin refer to
the facts x∈x. Questions: models? oscillation? grounding? verdicts?
"""

from ztl import T, F, Z, NOT, OPS2
from fixedpoint import EAGER, LAZY, fixed_points, iterate, least_fp_lazy, \
    ev_reg, fmt_v

# The universe: a=∅, b={b}, R={x: x∉x}, S={x: x∈x}
# Fact-sentences: 'x∈y'. Constant facts are literals T/F.
SETS = ["a", "b", "R"]

system = {}
for x in SETS:
    system[f"{x}∈a"] = "F"                        # a = ∅
    system[f"{x}∈b"] = "T" if x == "b" else "F"    # b = {b}
    system[f"{x}∈R"] = ("not", f"{x}∈{x}")         # Russell

sysS = {"S∈S": "S∈S"}                              # the twin — separately

if __name__ == "__main__":
    print("=" * 72)
    print("E11. RUSSELL ON ZTL-SETS: one quarantine cell, not a collapse")
    print("=" * 72)

    print("\n### The greedy jump: no models (Russell is homeless, like the liar)")
    fe = fixed_points(system, EAGER)
    print(f"  greedy fixed points: {len(fe)}")
    trace, loop = iterate(system, EAGER)
    period = len(trace) - loop if loop is not None else None
    print(f"  iteration from Z: cycle of period {period}")
    if period and period > 1:
        diffs = [k for k in trace[loop] if trace[loop][k] != trace[loop + 1][k]]
        print(f"  only these oscillate: {diffs} — the whole storm in two cells")

    print("\n### Lazy grounding: the universe stands, quarantine is pointwise")
    lfp = least_fp_lazy(system)
    q = sorted(k for k, v in lfp.items() if v == Z)
    g = sorted(k for k, v in lfp.items() if v != Z)
    print("  facts grounded: %d of %d" % (len(g), len(lfp)))
    for k in sorted(lfp):
        mark = "  ← QUARANTINE" if lfp[k] == Z else ""
        print(f"    {k} = {lfp[k]}{mark}")

    print("\n### Membership in R for ordinary residents — grounded and honest")
    print(f"  a∈R = {lfp['a∈R']} (a does not contain itself ⇒ Russell admits it)")
    print(f"  b∈R = {lfp['b∈R']} (b contains itself ⇒ Russell rejects it)")
    print("  Russell WORKS as a set for everyone except himself.")

    print("\n### Customs verdicts on the sore questions")
    v_notin = ev_reg(("not", "R∈R"), lfp, EAGER)
    print(f"  \"R ∈ R?\" — the atom is quarantined ({lfp['R∈R']}): not earned → refusal")
    print(f"  \"R ∉ R?\" — the greedy reading of ¬(R∈R): {v_notin} → also refusal")
    print("  Both questions get a refusal — the NaN signature on sets:")
    print("  neither Russell's membership nor non-membership in himself is earned.")

    print("\n### The twin S = {x : x ∈ x} — the truth-teller of set theory")
    fpS = fixed_points(sysS, EAGER)
    lfpS = least_fp_lazy(sysS)
    print(f"  S∈S: greedy models {len(fpS)} ({', '.join(fmt_v(v) for v in fpS)}),")
    print(f"  lazy grounding: {fmt_v(lfpS)} — underdetermination (the ID loop):")
    print("  classical solutions: TWO (admit/reject itself — both honest),")
    print("  for R∈R — ZERO. Even and odd, now in sets.")

    print("\n### Summary")
    print("  Classically (Frege): one cell R∈R blows up the WHOLE system —")
    print("  from a contradiction everything follows, naive set theory is dead.")
    print("  ZTL: the same cell goes into quarantine, the rest of the universe")
    print("  is grounded and works; Russell exists as a set with one unearned")
    print("  bit. Containment instead of explosion — because explosion demands")
    print("  an ASSERTED contradiction, and quarantine asserts nothing.")
    print("  Cf. the same author's VR-Sets: there Russell is excluded by")
    print("  GRAMMAR (forbidden to write); here he is admitted and defused.")
