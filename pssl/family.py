# -*- coding: utf-8 -*-
"""
family — PSSL leg 2, tack 2b: walking the parameter.

Leg 1 measured a 2/2 split among four grounds: classical and
intuitionistic have the deduction theorem, quantum MO2 and ZTL do not.
Tack 2a closed the quantum half into an impossibility. The question left
open is whether that split is ONE axis or two coincidences — the two
failures look different, non-commutation in a lattice versus the mark
reaching the operator.

Four is a sample, not a classification (PSSL says "at least four"). If
the parameter is real one should be able to WALK it, so this file adds
grounds and asks where the deduction theorem flips:

  K3   strong Kleene        third value undefined, designated {T}
  LP   Priest               the same tables, designated {T, u} — u is
                            "both", the paraconsistent dual of K3
  WK   weak Kleene          the infectious third value: any operation
                            touching u returns u. This is the cycle's own
                            LAZY REGISTER (kand/kor/knot), already
                            machine-checked in ZTL.lean
  Ł3   Łukasiewicz          the decisive one: three-valued like ZTL, ZTL's
                            nearest neighbour in the lineage, and it KEEPS
                            THE INVOLUTION THAT ZTL BREAKS (¬¬x = x)

Ł3 is where the contrast is sharpest. If it lands on the "has DT" side,
the split is not about three-valuedness and not about paracompleteness,
and ZTL's refusal is localised against the closest point outside it. If
it lands on the "no DT" side, the club is larger and the question becomes
what its members share.

Predictions are pre-registered in pssl/PREREGISTRATION_LEG2.md (Q2, Q3),
committed before this file was written.

Run:  python3 pssl/family.py
"""
import itertools
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
sys.path.insert(0, _ROOT)
sys.path.insert(0, _HERE)

import zipc                                                   # noqa: E402
import grounds as G                                           # noqa: E402

# Three matrix values. `u` is the third; what it MEANS differs per ground
# (undefined, both, unverified) and the tables say so, not the name.
TT, UU, FF = "1", "u", "0"
VALS = [TT, UU, FF]


# ---------------------------------------------------------------------------
# The matrices
# ---------------------------------------------------------------------------
def kleene_not(a):
    return {TT: FF, UU: UU, FF: TT}[a]


_ORD = {FF: 0, UU: 1, TT: 2}


def kleene_and(a, b):
    return a if _ORD[a] <= _ORD[b] else b


def kleene_or(a, b):
    return a if _ORD[a] >= _ORD[b] else b


def material_imp(a, b):
    return kleene_or(kleene_not(a), b)


def luk_imp(a, b):
    """Łukasiewicz: min(1, 1 - a + b) on {0, ½, 1}. The cell that matters
    is u→u = 1, where Kleene's material arrow gives u."""
    va, vb = _ORD[a] / 2.0, _ORD[b] / 2.0
    v = min(1.0, 1.0 - va + vb)
    return {0.0: FF, 0.5: UU, 1.0: TT}[v]


def weak(op):
    """Bochvar-internal infection: any operation touching u returns u."""
    def f(*args):
        return UU if UU in args else op(*args)
    return f


def weak_not(a):
    return UU if a == UU else kleene_not(a)


# ---------------------------------------------------------------------------
# A matrix ground: tables + designated set -> the two oracles
# ---------------------------------------------------------------------------
class Matrix:
    def __init__(self, name, refuses, neg, conj, disj, imp, designated):
        self.name, self.refuses = name, refuses
        self.neg, self.conj, self.disj, self.imp = neg, conj, disj, imp
        self.D = designated

    def ev(self, phi, asg):
        if isinstance(phi, str):
            return asg[phi]
        op = phi[0]
        if op == "not":
            return self.neg(self.ev(phi[1], asg))
        a, b = self.ev(phi[1], asg), self.ev(phi[2], asg)
        return {"and": self.conj, "or": self.disj,
                "imp": self.imp}[op](a, b)

    def _asgs(self, fs):
        names = sorted(set().union(*(G.atoms_of(f) for f in fs)))
        for combo in itertools.product(VALS, repeat=len(names)):
            yield dict(zip(names, combo))

    def valid(self, phi):
        return all(self.ev(phi, a) in self.D for a in self._asgs([phi]))

    def derives(self, premises, conclusion):
        fs = list(premises) + [conclusion]
        for a in self._asgs(fs):
            if all(self.ev(p, a) in self.D for p in premises) \
               and self.ev(conclusion, a) not in self.D:
                return False
        return True

    def involution(self):
        """¬¬x = x — the principle Ł3 keeps and ZTL breaks."""
        return all(self.neg(self.neg(v)) == v for v in VALS)


FAMILY = [
    Matrix("K3", "excluded middle; u is undefined",
           kleene_not, kleene_and, kleene_or, material_imp, {TT}),
    Matrix("LP", "explosion; u is BOTH (paraconsistent dual of K3)",
           kleene_not, kleene_and, kleene_or, material_imp, {TT, UU}),
    Matrix("weak Kleene", "everything touching u; the cycle's lazy register",
           weak_not, weak(kleene_and), weak(kleene_or), weak(material_imp),
           {TT}),
    Matrix("Lukasiewicz L3", "excluded middle; KEEPS the involution",
           kleene_not, kleene_and, kleene_or, luk_imp, {TT}),
]


# ---------------------------------------------------------------------------
# The deduction theorem, same real statement as leg 1
# ---------------------------------------------------------------------------
def dt_gap(valid, derives, pool, ctx_sizes=(0, 1)):
    """Γ, γ ⊨ φ ⟹ Γ ⊨ γ → φ. Returns (gap, holding, first witness)."""
    gap = hold = 0
    first = None
    for k in ctx_sizes:
        ctxs = [[]] if k == 0 else [[c] for c in pool]
        for ctx in ctxs:
            for gamma in pool:
                for phi in pool:
                    if not derives(ctx + [gamma], phi):
                        continue
                    hold += 1
                    disch = ("imp", gamma, phi)
                    ok = valid(disch) if not ctx else derives(ctx, disch)
                    if not ok:
                        gap += 1
                        if first is None:
                            first = (ctx, gamma, phi)
    return gap, hold, first


def modus_ponens(derives):
    """p, p→q ⊨ q — the arrow's TRANSPORT half."""
    return derives(["p", ("imp", "p", "q")], "q")


def discharge_gap(valid, derives, pool):
    """Arity-0 discharge: γ ⊨ φ ⟹ ⊨ γ→φ — the arrow's DISCHARGE half.
    Quadratic, so it runs on a deep pool where the cubic sweep cannot."""
    gap, first = 0, None
    for g in pool:
        for f in pool:
            if derives([g], f) and not valid(("imp", g, f)):
                gap += 1
                if first is None:
                    first = (g, f)
    return gap, first


# ---------------------------------------------------------------------------
# Why three of the zeros in the table are NOT tier C
#
# Found in review by Claude Fable 5 (2026-07-20) and banked here rather
# than left in a scratchpad. A zero from a sweep is the absence of a
# counterexample we could reach; these three are arguments instead, and
# they hold at every arity and every depth.
# ---------------------------------------------------------------------------
def lp_export_is_a_theorem():
    """LP's export-DT, pointwise, at EVERY arity — not a swept zero.

    In LP the arrow is material and the designated set is {1, u}. A
    discharged form γ→φ is UNdesignated only at value 0, and
    max(1-γ, φ) = 0 forces γ = 1 and φ = 0. But then γ is designated and
    φ is not, so the same valuation already refutes the RULE. Hence no
    countermodel to the discharge can fail to be a countermodel to the
    premise — export holds, and no sweep is needed to see it."""
    o = {FF: 0.0, UU: 0.5, TT: 1.0}
    return all(max(1.0 - o[g], o[f]) != 0.0 or (g == TT and f == FF)
               for g in VALS for f in VALS)


def no_tautologies(m):
    """K3 and weak Kleene have NO valid formulas at all — not 'none found
    up to size 5'. Send every atom to u: in K3 every connective returns u
    on all-u inputs, and in weak Kleene u is infectious. u is not
    designated in either, so nothing is valid, and no law can ever
    separate them from each other."""
    return all(m.ev(f, {a: UU for a in ("p", "q")}) not in m.D
               for f in zipc.build_pool(("p", "q"), depth=2))


if __name__ == "__main__":
    print("=" * 78)
    print("LEG 2, TACK 2b — WALKING THE PARAMETER")
    print("  Four was a sample. Where does the deduction theorem flip?")
    print("=" * 78)

    shallow = zipc.build_pool(("p", "q"), depth=1)
    deep = zipc.build_pool(("p", "q"), depth=2)
    print(f"\n  pools: depth 1 = {len(shallow)} formulas (cubic sweep, all")
    print(f"         grounds); depth 2 = {len(deep)} formulas (quadratic")
    print(f"         sweep, matrix grounds — the IPC prover is too slow)")

    print(f"\n  A DEPTH-1 ZERO IS NOT A THEOREM. Reported first because we")
    print(f"  nearly shipped one: Ł3 shows gap 0 at depth 1 and 6404 at")
    print(f"  depth 2. The counterexample p ⊨ ¬(p→¬p), ⊭ p→¬(p→¬p) has")
    print(f"  depth 3 and the shallow pool cannot contain it.")

    # ---------------------------------------------------------------
    print(f"\n{'=' * 78}\nTHE ARROW HAS TWO HALVES\n{'=' * 78}")
    print("  transport (modus ponens)  — the arrow carries earned truth")
    print("  discharge (deduction thm) — a rule can be exported into the")
    print("                              object language as an arrow\n")
    print("  NOTE ON DIRECTION. 'DT' here is the EXPORT direction,")
    print("  Γ,γ ⊨ φ ⟹ Γ ⊨ γ→φ. Export alone is cheap — a constant-⊤")
    print("  arrow has it and no modus ponens — which is exactly why the")
    print("  two columns are reported as a pair and neither alone means")
    print("  anything. (The Lean impossibility for MO2 is stronger still:")
    print("  it kills the BICONDITIONAL for every possible arrow.)\n")
    print("  A ground HAS the deduction theorem only if discharge holds at")
    print("  EVERY arity. Reporting arity-0 alone would put MO2 in the wrong")
    print("  column — it discharges at arity 0 and fails at arity 1, and no")
    print("  arrow can fix that (lean/QuantumWitness.lean).\n")
    print(f"  {'ground':22s}{'¬¬x=x':>8s}{'MP':>6s}{'DT':>6s}"
          f"{'arity-0 gap':>13s}   first arity-0 witness")

    rows = []
    for name, _refuses, valid, derives in G.GROUNDS:
        mp = modus_ponens(derives)
        g0, first = discharge_gap(valid, derives, shallow)   # slow oracles
        g1, _, _ = dt_gap(valid, derives, shallow, ctx_sizes=(1,))
        dt = (g0 == 0 and g1 == 0)
        w = f"{first[0]} ⊨ {first[1]}" if first else "—"
        print(f"  {name:22s}{'—':>8s}{'yes' if mp else 'NO':>6s}"
              f"{'yes' if dt else 'no':>6s}{g0:>13d}   {w}")
        rows.append((name, mp, dt, g0))

    print()
    for m in FAMILY:
        mp = modus_ponens(m.derives)
        g0, first = discharge_gap(m.valid, m.derives, deep)   # fast matrices
        g1, _, _ = dt_gap(m.valid, m.derives, shallow, ctx_sizes=(1,))
        dt = (g0 == 0 and g1 == 0)
        w = f"{first[0]} ⊨ {first[1]}" if first else "—"
        print(f"  {m.name:22s}{'yes' if m.involution() else 'no':>8s}"
              f"{'yes' if mp else 'NO':>6s}{'yes' if dt else 'no':>6s}"
              f"{g0:>13d}   {w}")
        rows.append((m.name, mp, dt, g0))

    # ---------------------------------------------------------------
    print(f"\n{'=' * 78}\nWHAT THE FAMILY SHOWS\n{'=' * 78}")
    both = [n for n, mp, dt, _ in rows if mp and dt]
    no_dt = [n for n, mp, dt, _ in rows if mp and not dt]
    no_mp = [n for n, mp, dt, _ in rows if not mp]
    print(f"  BOTH halves        : {', '.join(both)}")
    print(f"  keeps MP, no DT    : {', '.join(no_dt)}")
    print(f"  keeps DT, no MP    : {', '.join(no_mp)}")
    print()
    print("  Among the eight, only the classical and intuitionistic grounds")
    print("  keep both halves of the arrow. Every other ground here pays")
    print("  with one of the two — and no ground pays with neither.")
    print()
    print("  ZTL and LP are the two poles of the same trade: ZTL keeps")
    print("  transport and loses discharge (p ⊨ p, yet p→p falls); LP keeps")
    print("  discharge and loses transport (modus ponens is not valid).")
    print("  That is the cycle's own rules-versus-laws split, appearing")
    print("  again as a property of a FAMILY rather than of one logic.")

    # ---------------------------------------------------------------
    print(f"\n{'=' * 78}\nTHREE ZEROS THAT ARE NOT TIER C\n{'=' * 78}")
    print("  A zero from a sweep is the absence of a counterexample we")
    print("  could reach. These three are arguments, at every arity and")
    print("  every depth (found in review, 2026-07-20):\n")
    lp_ok = lp_export_is_a_theorem()
    K3 = [m for m in FAMILY if m.name == "K3"][0]
    WK = [m for m in FAMILY if m.name == "weak Kleene"][0]
    k3_ok, wk_ok = no_tautologies(K3), no_tautologies(WK)
    print(f"  LP export-DT is pointwise (γ→φ = 0 iff γ=1, φ=0) : {lp_ok}")
    print(f"  K3 has NO valid formulas at all (all-u)          : {k3_ok}")
    print(f"  weak Kleene likewise (u is infectious)           : {wk_ok}")
    print("  => K3 and weak Kleene cannot be separated by any LAW, ever;")
    print("     only a rule can tell them apart (and one does: p ⊨ p∨q).")
    assert lp_ok and k3_ok and wk_ok, "a banked argument stopped holding"

    # ---------------------------------------------------------------
    print(f"\n{'=' * 78}\nAT WHICH ARITY DOES DISCHARGE FIRST FAIL?\n{'=' * 78}")
    print("  Leg 1 asked: one axis or two? The counts do not answer it;")
    print("  the WITNESSES do.\n")
    allg = [(n, v, d) for n, _, v, d in G.GROUNDS] + \
           [(m.name, m.valid, m.derives) for m in FAMILY]
    shapes = {}
    print(f"  {'ground':22s}{'arity 0':>10s}{'arity 1':>10s}{'first at':>10s}")
    for nm, valid, derives in allg:
        g0, _, _ = dt_gap(valid, derives, shallow, ctx_sizes=(0,))
        g1, _, _ = dt_gap(valid, derives, shallow, ctx_sizes=(1,))
        at = "—" if (g0 == 0 and g1 == 0) else (0 if g0 else 1)
        shapes[nm] = at
        print(f"  {nm:22s}{g0:>10d}{g1:>10d}{str(at):>10s}")
    a0 = [n for n, v in shapes.items() if v == 0]
    a1 = [n for n, v in shapes.items() if v == 1]
    print(f"\n  loses discharge at arity 0 : {', '.join(a0)}")
    print(f"  loses it only at arity 1   : {', '.join(a1)}")
    print()
    print("  TWO SHAPES, not one axis. The three-valued grounds lose the")
    print("  arrow's identity itself; the ortholattice keeps identity")
    print("  (x →s x = ⊤) and loses only discharge under a standing")
    print("  context. Leg 1's 2/2 split lumped them together.")

    # ---------------------------------------------------------------
    print(f"\n{'=' * 78}\nPREDICTIONS\n{'=' * 78}")
    l3 = dict((n, g) for n, _, _, g in rows)["Lukasiewicz L3"]
    wk = dict((n, g) for n, _, _, g in rows)["weak Kleene"]
    print(f"  Q2 — Ł3 HAS the deduction theorem : FAILS  (gap {l3})")
    print("       Retracted, and the way it nearly passed is the point:")
    print("       at depth 1 it reads 0. A pool is not a proof.")
    print(f"  Q3 — weak Kleene LACKS it         : HOLDS  (gap {wk})")
    assert l3 > 0, "L3 lost its counterexample"
    assert wk > 0, "Q3 flipped"
    assert set(a0) and set(a1), "the two shapes collapsed"
    assert both == ["classical", "intuitionistic"], "the both-halves club changed"
    print("\n  TACK 2b GREEN — Q2 retracted on evidence, Q3 held,")
    print("  and the family showed something neither predicted.")
