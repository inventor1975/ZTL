# -*- coding: utf-8 -*-
"""
Expedition E15: Craig interpolation — bought with expressive completeness.

THEOREM (semantic construction): if A ⊨ B, there is an interpolant I
over the SHARED atoms only, with A ⊨ I and I ⊨ B. Construction: I is
the J-DNF of the projection "some completion of A's private atoms makes
A true" — an external function of the shared atoms, hence a formula
(E14: every external function is expressible).

Why it works: A ⊨ I — the witness is A's own valuation; I ⊨ B — glue
the A-witness (for the private-A part) to the current valuation (for
the private-B part): B does not read A's private atoms.

Measured totally on pools; the empty-shared-set edge needs constants
(⊤ is definable only with a spare variable — an honest caveat, printed).
"""

from itertools import product

from ztl import T, F, Z, VALUES, ev, atoms, all_envs
from entailment import entails

# formula-level J-indicators (E14)
JT = lambda x: ("and", x, x)
JF = lambda x: ("and", ("not", x), ("not", x))
JZ = lambda x: ("not", ("xnor", x, x))
IND = {T: JT, F: JF, Z: JZ}


def interpolant(A, B):
    """J-DNF of the projection of A onto the shared atoms."""
    shared = sorted(atoms(A) & atoms(B))
    privA = sorted(atoms(A) - set(shared))
    cells = []
    for combo in product(VALUES, repeat=len(shared)):
        sigma = dict(zip(shared, combo))
        # does some reading of A's private atoms make A true?
        witness = any(ev(A, {**sigma, **dict(zip(privA, c2))}) == T
                      for c2 in product(VALUES, repeat=len(privA)))
        if witness:
            conj = None
            for var in shared:
                lit = IND[sigma[var]](var)
                conj = lit if conj is None else ("and", conj, lit)
            cells.append(conj)
    if not cells:
        return "F"                       # constant: A unsatisfiable
    if cells[0] is None:
        return "T"                       # empty shared set, A satisfiable
    out = cells[0]
    for c in cells[1:]:
        out = ("or", out, c)
    return out


def pool(v1, v2):
    """Formulas over two atoms, depth ≤ 2."""
    a = [v1, v2, ("not", v1), ("not", v2)]
    out = list(a)
    for op in ("and", "or", "imp", "xor", "xnor"):
        for x in a[:2]:
            for y in a:
                out.append((op, x, y))
    return out


if __name__ == "__main__":
    print("=" * 72)
    print("E15. CRAIG INTERPOLATION: PAID FOR BY EXPRESSIVE COMPLETENESS")
    print("=" * 72)

    # A over {p, s}, B over {s, q}: shared = {s}
    As = pool("p", "s")
    Bs = pool("s", "q")
    total = bad = 0
    entailing = 0
    for A in As:
        for B in Bs:
            if entails([A], B) is not None:
                continue                  # only pairs with A ⊨ B
            entailing += 1
            I = interpolant(A, B)
            okV = atoms(I) <= (atoms(A) & atoms(B))
            ok1 = entails([A], I) is None
            ok2 = entails([I], B) is None
            total += 1
            if not (okV and ok1 and ok2):
                bad += 1
                print(f"  ✗ A={A}  B={B}  I={I}  "
                      f"vars⊆shared:{okV} A⊨I:{ok1} I⊨B:{ok2}")
    print(f"\n### Shared atom {{s}}: entailing pairs A ⊨ B: {entailing}")
    print(f"  interpolants constructed and verified: {total - bad} of {total}"
          f"  ({'✓ INTERPOLATION HOLDS, total on the pool' if bad == 0 else '✗'})")

    # sample with two shared atoms
    As2 = pool("p", "s")[:12]
    Bs2 = [("or", "s", "q"), ("imp", "s", "q"), ("and", "s", "s"),
           ("xnor", "s", "q"), ("not", ("and", "s", ("not", "s")))]
    t2 = b2 = 0
    for A in As2:
        for B in Bs2:
            if entails([A], B) is not None:
                continue
            I = interpolant(A, B)
            if not (atoms(I) <= (atoms(A) & atoms(B))
                    and entails([A], I) is None
                    and entails([I], B) is None):
                b2 += 1
            t2 += 1
    print(f"\n### Cross-sample: verified {t2 - b2} of {t2}"
          f" ({'✓' if b2 == 0 else '✗'})")

    # the empty-shared-set edge: constants are needed
    A0, B0 = ("and", "p", ("not", "p")), ("or", "q", "q")
    I0 = interpolant(A0, B0)
    print(f"\n### Edge: disjoint atoms, A = p∧¬p (unsat) ⊨ B = q∨q; I = {I0}")
    print(f"  A ⊨ I: {entails([A0], I0) is None};  I ⊨ B: "
          f"{entails([I0], B0) is None};  I is a CONSTANT — honest caveat:")
    print("  with an empty shared set the interpolant needs constants ⊤/⊥;")
    print("  in the pure language ⊤ = ¬(x∧¬x) spends a spare variable —")
    print("  the standard constant-free caveat, same as classically.")

    print("\n### Summary")
    print("  Craig interpolation holds, and the proof is one line on top of")
    print("  E14: the projection of A onto the shared atoms is an external")
    print("  function, every external function is a formula, and the J-DNF")
    print("  of the projection interpolates. Another box of \"completeness")
    print("  as a logic\" closed by the same coin.")
    if bad or b2:
        raise SystemExit("INTERPOLATION FAILED — stop.")
