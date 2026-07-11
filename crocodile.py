# -*- coding: utf-8 -*-
"""
Expedition E4: the crocodile paradox.

The crocodile: "I shall return the child ⟺ you guess what I will do."
The mother: "You will NOT return the child."

Formalization: R = "will return"; M = the prediction with content ¬R;
the deal: R ↔ M. The system: R copies M, M inverts R — Jourdain's
carousel (cycle 2, one inversion, odd). Control: an optimistic mother
("you will return"): M = R — zero inversions, even.

Questions for the instruments: models? oscillation? grounding? and the
main one — the greedy verdict on the DEAL ITSELF (R ↔ M) at the
grounded point.
"""

from ztl import T, F, Z, VALUES
from fixedpoint import EAGER, LAZY, fixed_points, iterate, least_fp_lazy, \
    ev_reg, fmt_v

CASES = {
    "pessimistic mother: M = ¬Tr(R)  [the classical paradox]":
        {"R": "M", "M": ("not", "R")},
    "optimistic mother:  M = Tr(R)   [control]":
        {"R": "M", "M": "R"},
}

DEAL = ("xnor", "R", "M")   # the crocodile's deal: "I return ⟺ you guessed"

for title, system in CASES.items():
    print(f"### {title}")
    fe = fixed_points(system, EAGER)
    print(f"  greedy models: {', '.join(map(fmt_v, fe)) or 'NONE'}")
    trace, loop = iterate(system, EAGER)
    period = len(trace) - loop if loop is not None else None
    if period and period > 1:
        print(f"  greedy iteration from Z: CYCLE of period {period}: "
              + " → ".join(fmt_v(v) for v in trace[loop:]))
    else:
        print(f"  greedy iteration from Z: converged to {fmt_v(trace[-1])}")
    lfp = least_fp_lazy(system)
    q = [k for k, v in lfp.items() if v == Z]
    print(f"  lazy grounding: {fmt_v(lfp)}   quarantine: {q or 'empty'}")
    verdict = ev_reg(DEAL, lfp, EAGER)
    print(f"  greedy verdict on the deal R↔M at the point: {verdict}"
          + ("  ← THE DEAL DOES NOT EARN TRUTH" if verdict != T else
             "  (the deal is enforceable)"))
    print()

print("Conclusion: the pessimist closes an odd cycle (1 inversion) — by the")
print("parity theorem there are no models; the crocodile can neither keep")
print("his word nor break it. The zero-trust diagnosis: the deal's condition")
print("(\"you guessed\") cannot be grounded, the deal R↔M evaluates greedily")
print("to F — THE CONTRACT IS VOID, no obligation ever arose. The optimist")
print("gives an even cycle: two honest models (returns / does not return,")
print("the word kept in both) — but which one realizes, the deal does not")
print("determine: the crocodile chooses himself.")
