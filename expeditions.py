# -*- coding: utf-8 -*-
"""
Expeditions into the open ocean: Curry, the parity theorem, Yablo.

Instruments — from fixedpoint.py (greedy/lazy jumps, fixed points).

E1. CURRY: c = (Tr(c) → ⊥). Explodes without negation — breaks many
    paraconsistent approaches. Question: does our quarantine extinguish
    it by the same mechanics as the liar?
E2. PARITY: a cycle s₀→s₁→…→s₀, each edge either "copy" or "invert".
    Hypothesis (the XOR bookkeeper): classical models exist ⟺ the
    number of inversions is even. Total check: all cycles of length
    1–5, all inversion patterns.
E3. YABLO: sᵢ = "all subsequent ones are false" (without a single
    cycle!). The infinite version is paradoxical; what do finite
    truncations see?
"""

from itertools import product

from ztl import T, F, Z, VALUES
from fixedpoint import (EAGER, LAZY, fixed_points, iterate, least_fp_lazy,
                        jump, ev_reg, fmt_v)


def expedition_curry():
    print("### E1. CURRY: c = (Tr(c) → ⊥)")
    system = {"c": ("imp", "c", "F")}
    fe = fixed_points(system, EAGER)
    fl = fixed_points(system, LAZY)
    print(f"  greedy fixed points: {', '.join(map(fmt_v, fe)) or 'NONE'}")
    print(f"  lazy fixed points: {', '.join(map(fmt_v, fl)) or 'NONE'}")
    trace, loop = iterate(system, EAGER)
    period = len(trace) - loop if loop is not None else None
    cyc = " → ".join(fmt_v(v) for v in trace[loop:]) if period and period > 1 else ""
    print(f"  greedy iteration from Z: {'CYCLE of period ' + str(period) + ': ' + cyc if period and period > 1 else 'converged'}")
    lfp = least_fp_lazy(system)
    print(f"  lazy grounding: {fmt_v(lfp)} — quarantine: "
          f"{[k for k, v in lfp.items() if v == Z] or 'empty'}")
    content = ev_reg(system["c"], lfp, EAGER)
    print(f"  greedy verdict on the content of c: {content}")
    print("  Conclusion: Curry is homeless greedily and grounded lazily — the SAME")
    print("  mechanics as the liar, though it contains no negation: quarantine")
    print("  does not care which operator a sentence used to invert itself.")


def cycle_system(pattern):
    """A cycle: s_i defined via s_{i+1 mod n}; pattern[i]=1 — inversion."""
    n = len(pattern)
    sys_ = {}
    for i, inv in enumerate(pattern):
        ref = f"s{(i + 1) % n}"
        sys_[f"s{i}"] = ("not", ref) if inv else ref
    return sys_


def expedition_parity(max_n=5):
    print("\n### E2. PARITY THEOREM: all cycles of length 1..%d, all patterns" % max_n)
    checked = bad = 0
    for n in range(1, max_n + 1):
        for pattern in product((0, 1), repeat=n):
            system = cycle_system(pattern)
            classical = [v for v in fixed_points(system, EAGER)
                         if all(x in (T, F) for x in v.values())]
            even = sum(pattern) % 2 == 0
            checked += 1
            if bool(classical) != even:
                bad += 1
                print(f"  ✗ n={n} pattern={pattern}: inversions {sum(pattern)}, "
                      f"classical models {len(classical)}")
    print(f"  cycles checked: {checked}")
    if not bad:
        print("  ✓ HYPOTHESIS CONFIRMED TOTALLY: classical models exist")
        print("    ⟺ the number of inversions around the ring is even (XOR-sum 0).")
        print("    Odd rings are carousels (liar n=1, Jourdain n=2, ...);")
        print("    even rings are truth-tellers (underdetermination, not paradox).")
    return checked, bad


def yablo_system(n):
    """Yablo truncation: s_i = ⋀_{j>i} ¬Tr(s_j); the last one — empty conjunction T."""
    sys_ = {}
    for i in range(n):
        parts = [("not", f"s{j}") for j in range(i + 1, n)]
        if not parts:
            phi = "T"
        else:
            phi = parts[0]
            for p in parts[1:]:
                phi = ("and", phi, p)
        sys_[f"s{i}"] = phi
    return sys_


def expedition_yablo(max_n=6):
    print("\n### E3. YABLO (truncations): s_i = \"all subsequent ones are false\"")
    for n in range(2, max_n + 1):
        system = yablo_system(n)
        lfp = least_fp_lazy(system)
        quarantined = [k for k, v in lfp.items() if v == Z]
        fe = fixed_points(system, EAGER)
        vals = "".join(lfp[f"s{i}"] for i in range(n))
        print(f"  n={n}: grounding {vals} (s0 leftmost), quarantine "
              f"{quarantined or 'EMPTY'}, greedy models {len(fe)}")
    print("  Conclusion: EVERY finite truncation is fully grounded (the last one")
    print("  vacuously true, the rest false) — no paradox at any n.")
    print("  Yablo's paradox lives ONLY at actual infinity: unlike the carousels")
    print("  (finite rings), it cannot be caught by a finite instrument — and")
    print("  cannot be accused of circularity. Infinite regress is a separate,")
    print("  third source of ungroundedness.")


if __name__ == "__main__":
    print("=" * 72)
    print("EXPEDITIONS: CURRY, PARITY, YABLO")
    print("=" * 72)
    expedition_curry()
    expedition_parity()
    expedition_yablo()
