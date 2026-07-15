# -*- coding: utf-8 -*-
"""
pengine — the paradox engine. Paradoxes as the range of ONE construction.

The seam (curator's intuition, "a paradox IS an operator"): a self-referential
sentence net is  S_i = f_i(S_1..S_n);  a paradox is what the net DOES, read
operationally.

What the engine MEASURED while cranking (two corrections to the naive story):

  1. The zero-trust GROUNDING (lazy least fixed point) is too COARSE to tell
     paradoxes apart: every pure self-reference (Liar, carousel, every cycle,
     Yablo) grounds uniformly to Z. The discriminator is not the grounding — it
     is the set of CLASSICAL SOLUTIONS of the net (assignments in {T,F} that
     satisfy every S_i = f_i).

  2. For a NEGATION cycle the number of solutions is a parity / graph fact:
        odd  cycle  → 0 solutions → contradictory   (Liar-type)
        even cycle  → 2 solutions → underdetermined  (truth-teller-type)
     i.e. paradoxical ⟺ the reference graph is NOT 2-colourable (not bipartite).
     (This is the graph theory of paradox — Cook, Walicki — reached here by
     measurement, one handle for it.)

So the operational reading: a paradox is a self-referential net whose
fixed-point equations have NO unique classical solution — 0 (over-constrained,
contradictory) or ≥2 (under-constrained, undetermined) — and ZTL then withholds
(grounds to Z) rather than picking. Names provisional.
"""

from itertools import product

from ztl import T, F, Z, ev
from fixedpoint import least_fp_lazy

HOLE = "S"                                   # the self-reference placeholder


def solutions(net):
    """Classical solutions: assignments in {T,F} with S_i = f_i for all i —
    the fixed points of the reference net. THE discriminator."""
    names = sorted(net)
    out = []
    for combo in product((T, F), repeat=len(names)):
        v = dict(zip(names, combo))
        if all(ev(net[n], v) == v[n] for n in names):
            out.append(v)
    return out


def ground(net):
    """The zero-trust verdict: the lazy least fixed point (cautious — pure
    self-reference lands in Z)."""
    return least_fp_lazy(net)


def diagnose(net):
    """The operational diagnosis of a reference net."""
    sols = solutions(net)
    g = ground(net)
    n = len(sols)
    kind = ("contradictory  (0 solutions, Liar-type)" if n == 0 else
            "determined     (1 solution)" if n == 1 else
            f"underdetermined ({n} solutions, truth-teller-type)")
    return {"solutions": sols, "ground": g, "n": n, "kind": kind}


def selfref(f):
    """Convenience for a one-sentence net S = f(S)."""
    return diagnose({HOLE: f})


def neg_cycle(k):
    """The k-sentence negation cycle A1=¬A2, …, Ak=¬A1."""
    ns = [f"A{i}" for i in range(1, k + 1)]
    return {ns[i]: ("not", ns[(i + 1) % k]) for i in range(k)}


# specimens, each a reference net -------------------------------------------
ZOO = {
    "Liar          S=¬S":        {HOLE: ("not", HOLE)},
    "truth-teller  S=S":         {HOLE: HOLE},
    "Curry         S=S→⊥":       {HOLE: ("imp", HOLE, "F")},
    "contra        S=S∧¬S":      {HOLE: ("and", HOLE, ("not", HOLE))},
    "Russell-shadow R∈R↔¬(R∈R)": {HOLE: ("not", HOLE)},
    "carousel      A=B,B=¬A":    {"A": "B", "B": ("not", "A")},
    "even cycle    A=¬B,B=¬A":   {"A": ("not", "B"), "B": ("not", "A")},
}


def report_zoo():
    print("THE ZOO AS reference nets — solutions discriminate, grounding does not\n")
    for name, net in ZOO.items():
        d = diagnose(net)
        gz = "Z (quarantine)" if any(v == Z for v in d["ground"].values()) \
            else ", ".join(f"{k}={v}" for k, v in d["ground"].items())
        print(f"  {name}")
        print(f"      solutions: {d['n']}  →  {d['kind']}")
        print(f"      grounding: {gz}\n")


def parity_law():
    print("NEGATION CYCLES — paradoxical ⟺ odd (reference graph not 2-colourable)\n")
    print(f"  {'k':>2} {'#sol':>5} {'ground':>7}   verdict")
    for k in range(1, 7):
        d = diagnose(neg_cycle(k))
        g = "Z" if any(v == Z for v in d["ground"].values()) else "value"
        v = "contradictory (odd)" if d["n"] == 0 else \
            f"{d['n']} solutions (even)"
        print(f"  {k:>2} {d['n']:>5} {g:>7}   {v}")
    print("\n  odd k → 0 solutions (Liar-type); even k → 2 (truth-teller-type);"
          "\n  grounding says Z for all — the STRUCTURE is in the solutions.")


if __name__ == "__main__":
    report_zoo()
    print("=" * 64 + "\n")
    parity_law()
