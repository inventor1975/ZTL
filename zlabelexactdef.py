# -*- coding: utf-8 -*-
"""
Expedition E60: THE RECEIPT NAMES NOTHING IDLE ON A LINEAR CLAIM — UNDER A
DEFINITE READING OF THE OTHER GROUNDS.

`label_exact_linear` (LabelExact.lean) proves exactness with `pivotal`, whose
reading of the other unverified atoms may stay PARTIAL. §19 said "definite";
E59 found the gap and softened the prose. `lean/LabelExactDefinite.lean` proves
the strong form (`label_exact_linear_definite`, empty axiom list), as a layer
over the partial theorem: drive the Z side with `drivable`, keep the definite
side by monotonicity, fill the rest.

Measured here with the judge's own `_lazy`: every pending LINEAR cell of the
exhaustive depth ≤ 2 pool over three atoms, all 27 markings; for every named
atom, is there a DEFINITE reading of the other unverified atoms (each T or F,
never Z) under which a := T and a := F give different lazy verdicts? And the
negative control: OUTSIDE the linear class the same census must find named
atoms that are not — `p ∧ ¬p` first among them — or the linearity hypothesis
would be decoration.
"""
import itertools
from ztl import T, F, Z
from ztljudge import _lazy

OPS = ("and", "or", "imp", "xor", "xnor")
A = ("p", "q", "r")


def pivotal_definite(phi, m, a, atoms):
    others = [x for x in atoms if x != a and m[x] == Z]
    for vals in itertools.product((T, F), repeat=len(others)):
        w = dict(m); w.update(zip(others, vals))
        w1 = dict(w); w1[a] = T
        w2 = dict(w); w2[a] = F
        if _lazy(phi, w1)[0] != _lazy(phi, w2)[0]:
            return True
    return False


def occ(f, a):
    if isinstance(f, str):
        return 1 if f == a else 0
    return sum(occ(x, a) for x in f[1:])


def pool():
    d0 = list(A)
    d1 = [("not", a) for a in d0] + [(op, a, b) for op in OPS for a in d0 for b in d0]
    base = d0 + d1
    d2 = [("not", f) for f in d1] + [(op, a, b) for op in OPS for a in base for b in base]
    out, seen = [], set()
    for f in d0 + d1 + d2:
        if f not in seen:
            seen.add(f); out.append(f)
    return out


def main():
    print("=" * 72)
    print("E60. ON A LINEAR CLAIM EVERY NAMED ATOM DECIDES UNDER A DEFINITE READING")
    print("=" * 72)
    P = pool()
    lin_cells = lin_named = lin_fail = 0
    non_cells = non_named = non_fail = 0
    first_nonlinear_fail = None
    for phi in P:
        for combo in itertools.product((T, F, Z), repeat=3):
            m = dict(zip(A, combo))
            lv, lab = _lazy(phi, m)
            if lv != Z:
                continue
            linear = all(occ(phi, a) <= 1 for a in A if m[a] == Z)
            if linear:
                lin_cells += 1
                for a in lab:
                    lin_named += 1
                    if not pivotal_definite(phi, m, a, A):
                        lin_fail += 1
                        print(f"  ✗ LINEAR FAILURE {phi} {m} atom {a}")
            else:
                non_cells += 1
                for a in lab:
                    non_named += 1
                    if not pivotal_definite(phi, m, a, A):
                        non_fail += 1
                        if first_nonlinear_fail is None:
                            first_nonlinear_fail = (phi, {k: v for k, v in m.items()}, a)
    print(f"  pool: {len(P)} formulas of depth ≤ 2 over p, q, r × 27 markings")
    print(f"  LINEAR pending cells {lin_cells}; named atoms {lin_named}; not definite-pivotal: {lin_fail}")
    print(f"  NON-linear pending cells {non_cells}; named atoms {non_named}; not definite-pivotal: {non_fail}"
          f" ({100 * non_fail // non_named if non_named else 0}%)")
    clash = ("and", "p", ("not", "p"))
    mZ = {"p": Z, "q": Z, "r": Z}
    lv, lab = _lazy(clash, mZ)
    clash_ok = (lv == Z and "p" in lab and not pivotal_definite(clash, mZ, "p", A))
    print(f"  control p ∧ ¬p at all-Z: named {'p' in lab}, definite-pivotal {not clash_ok} — "
          f"{'the hypothesis is load-bearing' if clash_ok else 'CONTROL FAILED'}")
    ok = lin_fail == 0 and lin_cells > 0 and non_fail > 0 and clash_ok
    print("\n  Reading: linearity buys exactness under definite readings, and nothing")
    print("  weaker does — the same census shows the failures outside the class.")
    print("\n" + ("E60 GREEN: zero linear failures, failures outside the class, the clash control holds"
                  if ok else "E60 RED"))
    return 0 if ok else 1


if __name__ == "__main__":
    import sys
    sys.exit(main())
