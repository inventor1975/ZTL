# -*- coding: utf-8 -*-
"""
Expedition E62: THE PRICE LIST ON THE NUMERIC FLOOR — commutativity and the unit
survive at the interval level and fall at the verdict.

`zarith.py` measured one cell (x ∈ [1,3], y ∈ [2,4]); `lean/ZNumPrice.lean` proves
the general statement over ZNum's reading semantics (every occurrence reads
independently): the reading sets of x+y and y+x, and of x+0 and x, coincide,
while the equations as atoms on a mark are neither forced true nor forced false.
Measured here on every pair of small intervals.
"""
import itertools


def readings_add(I, J):
    return {u + v for u in range(I[0], I[1] + 1) for v in range(J[0], J[1] + 1)}


def readings(I):
    return set(range(I[0], I[1] + 1))


def verdict_eq(A, B):
    """T if forced equal under all independent readings, F if forced unequal, else Z."""
    if all(a == b for a in A for b in B):
        return "T"
    if all(a != b for a in A for b in B):
        return "F"
    return "Z"


def main():
    print("=" * 72)
    print("E62. COMMUTATIVITY AND THE UNIT: SAME READINGS, NO EARNED EQUATION")
    print("=" * 72)
    ivs = [(lo, hi) for lo in range(-3, 4) for hi in range(lo, 4)]
    n = set_div = comm_forced = unit_forced = marks = comm_Z = unit_Z = 0
    for I in ivs:
        for J in ivs:
            n += 1
            if readings_add(I, J) != readings_add(J, I):
                set_div += 1
            if readings_add(I, (0, 0)) != readings(I):
                set_div += 1
            vc = verdict_eq(readings_add(I, J), readings_add(J, I))
            vu = verdict_eq(readings_add(I, (0, 0)), readings(I))
            if I[0] < I[1]:
                marks += 1
                comm_Z += (vc == "Z"); unit_Z += (vu == "Z")
                comm_forced += (vc != "Z"); unit_forced += (vu != "Z")
    print(f"  interval pairs: {n}; reading-set divergences (x+y vs y+x, x+0 vs x): {set_div}")
    print(f"  cells where x is a mark (lo < hi): {marks}; eq(x+y, y+x) forced: {comm_forced}, Z: {comm_Z};"
          f" eq(x+0, x) forced: {unit_forced}, Z: {unit_Z}")
    I, J = (1, 3), (2, 4)
    print(f"  the zarith cell x∈[1,3], y∈[2,4]: eq(x+y, y+x) = {verdict_eq(readings_add(I, J), readings_add(J, I))},"
          f" eq(x+0, x) = {verdict_eq(readings_add(I, (0, 0)), readings(I))}")
    ok = set_div == 0 and comm_forced == 0 and unit_forced == 0 and marks > 0
    print("\n  Reading: the interval arithmetic inherits both laws; the verdict does not")
    print("  earn either equation on a mark — coincidence of bounds is not identity (R1).")
    print("\n" + ("E62 GREEN: reading sets coincide everywhere; no equation is forced on a mark"
                  if ok else "E62 RED"))
    return 0 if ok else 1


if __name__ == "__main__":
    import sys
    sys.exit(main())
