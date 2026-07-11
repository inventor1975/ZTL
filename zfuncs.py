# -*- coding: utf-8 -*-
"""
Expedition E7: functions over marked sets.

A function is a computation, not a verdict ⇒ by the two-register
theorem it behaves LAZILY: the mark flows through the function
(f(unverified) = unverified with a pedigree). This is exactly taint
tracking from security (Denning 1976): the Z-mark = taint, verdicts =
sanitizers.

Measurements: the image (verified collisions earn merging, marks keep
multiplicity), two preimages (verdict/solver), composition and taint
transitivity, injectivity (even id is not certified), law inheritance.
"""

from ztl import T, F, Z, OPS2
from zsets import ZSet, V_, M_, eq_atom, mem, sub, seteq, union, card_bounds

OR, AND = OPS2["or"], OPS2["and"]


class ZFun:
    """A verified function: a table on verified values.
    On marks — taint: the output is a new mark with a pedigree."""

    def __init__(self, name, table):
        self.name = name
        self.table = dict(table)

    def __call__(self, el):
        if el[0] == "V":
            return V_(self.table[el[1]])
        return M_(f"{self.name}({el[1]})")     # taint with a pedigree


def image(f, S):
    core = {f.table[x] for x in S.core}        # collisions are EARNED
    quar = tuple(f"{f.name}({i})" for i in S.quar)
    return ZSet(core, quar)


def compose(g, f, name=None):
    return ZFun(name or f"{g.name}∘{f.name}",
                {x: g.table[y] for x, y in f.table.items()})


def preimage_verdict(f, Tset, S):
    """Verdict preimage: only elements of S that EARNED f(x) ∈ T."""
    core = {x for x in S.core if mem(V_(f.table[x]), Tset) == T}
    return ZSet(core, ())                      # marks earn nothing

def preimage_possible(f, Tset, S):
    """Solver preimage: candidates (core classically + all marks)."""
    core = {x for x in S.core if mem(V_(f.table[x]), Tset) == T}
    return ZSet(core, S.quar)


def injective_verdict(f, S):
    """Injectivity on S — an ∀-fold over pairs: eq(f a, f b) → eq(a, b)?
    Verdict-wise: pairs involving a mark give Z-atoms in premise/conclusion."""
    els = S.elements()
    v = T
    for i, a in enumerate(els):
        for b in els[i + 1:]:
            # "distinct inputs ⇒ distinct outputs", contrapositively:
            # eq(f a, f b) → eq(a, b); atoms via eq_atom
            prem = eq_atom(f(a), f(b))
            concl = eq_atom(a, b)
            v = AND(v, OPS2["imp"](prem, concl))
    return v


if __name__ == "__main__":
    print("=" * 72)
    print("E7. FUNCTIONS OVER MARKED SETS (taint mode)")
    print("=" * 72)

    S = ZSet((1, 2, 3), ("m1",))               # {1,2,3,Z}
    f = ZFun("f", {1: 10, 2: 10, 3: 30})        # collision: f(1)=f(2)=10
    g = ZFun("g", {10: 100, 30: 100})           # collapses everything
    ident = ZFun("id", {1: 1, 2: 2, 3: 3})

    print("\n### The image: verified collisions earn merging")
    fS = image(f, S)
    print(f"  f{{1,2,3,Z}} = {fS}")
    lo, hi = card_bounds(fS)
    print(f"  |f(S)| ∈ [{lo},{hi}] — the core merged (f(1)=f(2) is PROVEN),")
    print("  the mark stayed a mark: taint is not laundered by a function.")

    print("\n### Composition: taint is transitive, the image is associative")
    gfS1 = image(g, image(f, S))
    gfS2 = image(compose(g, f), S)
    print(f"  g(f(S)) = {gfS1}")
    print(f"  (g∘f)(S) = {gfS2}")
    print(f"  representation coincided: {gfS1.core == gfS2.core and len(gfS1.quar) == len(gfS2.quar)}"
          f"   seteq verdict: {seteq(gfS1, gfS2)} — two levels again")
    print(f"  the mark's pedigree after g∘f: {gfS1.quar[0]}")

    print("\n### The preimage split in two (two-registeredness)")
    Tgt = ZSet((10,))
    pv = preimage_verdict(f, Tgt, S)
    pp = preimage_possible(f, Tgt, S)
    print(f"  verdict f⁻¹({{10}}) = {pv} — marks dropped (default deny)")
    print(f"  solver f⁻¹({{10}}) = {pp} — the mark remains a candidate")
    print(f"  verdict \"the preimage covers the candidates\": {sub(pp, pv)}")

    print("\n### Injectivity: even id is not certified on a marked domain")
    print(f"  id injective on {{1,2,3}} (clean): "
          f"{injective_verdict(ident, ZSet((1, 2, 3)))}")
    print(f"  id injective on {{1,2,3,Z}} (marked): "
          f"{injective_verdict(ident, S)}")
    print(f"  f (with a collision) on clean: "
          f"{injective_verdict(f, ZSet((1, 2, 3)))} — the collision is earned")
    print("  A pair (mark, anything) gives Z-atoms → the implication Z→Z = F →")
    print("  the ∀-fold collapses: an injectivity certificate requires a FULLY")
    print("  verified domain. The echo of the fallen \"S ⊆ S\".")

    print("\n### Laundering taint is forbidden; the sanitizer = external verification")
    m = M_("sensor")
    print(f"  f(mark) = {f(m)} — a mark (the pedigree grows)")
    print(f"  g(f(mark)) = {g(f(m))} — taint is transitive")
    print("  The only way to remove a mark is EXTERNAL verification of the value")
    print("  (not a function): in security terms — declassification only through")
    print("  proof. Perl taint mode, TaintDroid, Denning's IFC lattice —")
    print("  the third engineering twin of ZTL after NaN and NULL.")
