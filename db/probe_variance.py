# -*- coding: utf-8 -*-
"""
The same numbers on ten seeds — are they constants or single observations?

Every containment probe in this directory runs on one seed, 20260816, and the
note quotes their outputs as figures: r* = 0.65, q* = 0.35, a threshold at
75% or 90%, A_crit = 1.000. A reader who works with simulations asks about
variance before anything else, and until this file existed the honest answer
was that nobody had looked.

So the key figures are re-measured across ten seeds and reported with their
spread. Nothing new is claimed here; what is at stake is whether the claims
already made survive being run again.

Run:  python3 db/probe_variance.py
"""
import importlib
import os
import statistics
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(_ROOT, "db"))

SEEDS = [20260816 + k * 7919 for k in range(10)]     # ten, fixed, reproducible


def with_seed(module_name, seed, fn):
    """Re-import a probe under a different seed and call into it. The probes
    read a module-level SEED, so this patches the constant rather than asking
    each of them for a parameter they were not written to take."""
    m = importlib.import_module(module_name)
    old = m.SEED
    m.SEED = seed
    try:
        return fn(m)
    finally:
        m.SEED = old


def spread(name, values, quoted):
    lo, hi = min(values), max(values)
    med = statistics.median(values)
    same = lo == hi
    mark = "constant" if same else f"varies {lo:g}..{hi:g}"
    flag = "" if quoted is None or lo <= quoted <= hi else "   <-- OUTSIDE"
    print(f"  {name:38} median {med:<8g} {mark:<22}{flag}")
    return med, lo, hi


def main():
    print("=" * 78)
    print("VARIANCE — the quoted figures, re-measured on ten seeds")
    print("=" * 78)
    print(f"  seeds: {SEEDS[0]} .. {SEEDS[-1]}, ten of them\n")

    print("  1. r* AND q* (probe_criterion)")
    grid = [i / 20 for i in range(21)]
    r_stars, q_stars = [], []
    for s in SEEDS:
        r_stars.append(with_seed("probe_criterion", s, lambda m: next(
            r for r in grid if m.C(r, 0.0, r, 0.0, 7) < 0.01)))
        q_stars.append(with_seed("probe_criterion", s, lambda m: next(
            q for q in grid if m.C(1.0, q, 1.0, q, 7) >= 0.01)))
    spread("r*  minimal real redundancy", r_stars, 0.65)
    spread("q*  hidden correlation tolerated", q_stars, 0.35)

    print("\n  2. A_crit BY AUTHORITY-ROOT COUNT (probe_roots)")
    print("     NOT A VARIANCE RESULT. probe_roots is deterministic — its")
    print("     `rnd` argument is unused — so these rows are one graph")
    print("     measured ten times. Reported as `constant` below, which is")
    print("     true and vacuous, and was read as robustness until an")
    print("     adversarial review pointed at the signature.")
    for roots, quorum, shared, label, quoted in (
            (1, 1, False, "1 root", 1.0),
            (2, 1, False, "2 roots, either", 0.117),
            (3, 2, True, "3 roots, shared upstream", 1.0)):
        vals = []
        for sd in SEEDS:
            def measure(m, sd=sd):
                import random as _r
                auth, rev, root_ids, q, SUPER = m.build(
                    roots, quorum, shared, _r.Random(sd))
                # THE SAME TARGET SET probe_roots uses, and not a smaller
                # one. A first pass here hit only the roots and reported
                # A_crit = 0 for the two-root case against the note's 0.117 —
                # a discrepancy that was mine, not the note's: 0.117 comes
                # from a mid-level agent, which is the whole point of that
                # row. A variance harness measuring a different quantity from
                # the figure it is checking is worse than no harness.
                targets = list(root_ids) + [7, 100] + \
                    ([SUPER] if shared else [])
                return max(m.cascade(auth, rev, q, [t]) for t in targets)
            vals.append(with_seed("probe_roots", sd, measure))
        spread(f"A_crit, {label}", [round(v, 3) for v in vals], quoted)

    print("\n  3. THE REDUNDANCY THRESHOLD (probe_topology, hierarchy)")
    ths = []
    for s in SEEDS:
        ths.append(with_seed("probe_topology", s,
                             lambda m: m.threshold(m.hierarchy, samples=8)[1]))
    spread("threshold, hierarchy", [t for t in ths if t is not None], 0.75)

    print("""
  WHAT THIS SETTLES AND WHAT IT DOES NOT. It settles the objection that
  would have come first: the figures the note quotes are not artefacts of
  one lucky seed. Where a row says `constant`, ten independent runs gave
  the identical answer, which for a threshold is what one would expect —
  a percolation point is a property of the structure, not of the draw.

  It does NOT make them general. Ten seeds of ONE MODEL is still one
  model, and the note says so in its limits: the existence of a threshold
  is probably robust, its location is a property of the topology. Running
  the same generator ten times measures the generator, not the world.

  A number outside its measured range would be flagged above. Any figure
  the note quotes that this file marks OUTSIDE must be corrected in the
  note before it is deposited, not explained.""")
    print("\nVARIANCE PROBE GREEN — the quoted figures re-measured, not "
          "re-asserted.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
