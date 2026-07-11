# -*- coding: utf-8 -*-
"""
Expedition E5: sets with unverified elements (ZTL-sets).

Sets are NOT postulated — they are derived from the logic:
  * element equality eq(a,b) is an ATOM with value T/F/Z
    (verified-vs-verified — classical; any mark — Z: identity is not
    earned, even a mark against itself);
  * membership mem(x,S) = an ∃-fold of eq-atoms (a strict T-witness);
  * inclusion sub(S,T) = an ∀-fold of mem (all strictly T);
  * set equality seteq = sub ∧ sub.
Everything computes through the ztl.py tables — not a single special
rule.

Representation: ZSet = (core: frozenset of verified, quar: tuple of
marks). A mark ('Z', id) is an unverified observation; id is provenance
and does NOT participate in equality (zero-trust: provenance does not
prove identity).

Measurements: {Z,Z} versus {Z}; Z ∉ {Z}; set laws on clean and marked
sets; two levels of equality (representation versus verdict); interval
cardinality; comparison with SQL (NULL: = / IN / DISTINCT).
"""

from ztl import T, F, Z, OPS2, NOT

OR, AND, XNOR = OPS2["or"], OPS2["and"], OPS2["xnor"]


# --- elements ---
def V_(x):
    return ("V", x)          # verified value


def M_(ident):
    return ("Z", ident)      # unverified mark (quarantine)


def eq_atom(a, b):
    """Element equality — an atom: T/F for verified, Z with any mark."""
    if a[0] == "V" and b[0] == "V":
        return T if a[1] == b[1] else F
    return Z                 # identity not earned — even a mark with itself


# --- sets ---
class ZSet:
    def __init__(self, core=(), quar=()):
        self.core = frozenset(core)
        self.quar = tuple(quar)

    def elements(self):
        return [V_(x) for x in sorted(self.core, key=repr)] + \
               [M_(i) for i in self.quar]

    def __repr__(self):
        c = "{" + ", ".join(map(repr, sorted(self.core, key=repr))) + "}"
        return f"ZSet(core={c}, quar={len(self.quar)} marks)"

    # representation level (machine, not verdict)
    def repr_eq(self, other):
        return self.core == other.core and \
            sorted(self.quar) == sorted(other.quar)


def mem(x, S):
    """x ∈ S: an ∃-fold of eq-atoms through the tables (strict witness)."""
    v = F
    for el in S.elements():
        v = OR(v, eq_atom(x, el))
    return v


def sub(S, Tset):
    """S ⊆ T: an ∀-fold of memberships (all strictly T)."""
    v = T
    for el in S.elements():
        v = AND(v, mem(el, Tset))
    return v


def seteq(S, Tset):
    """S = T (verdict): mutual inclusion."""
    return AND(sub(S, Tset), sub(Tset, S))


# --- operations (representation level) ---
def union(S, Tset):
    return ZSet(S.core | Tset.core, S.quar + Tset.quar)


def intersect(S, Tset):
    # intersection demands PROVEN coincidence: marks prove nothing
    return ZSet(S.core & Tset.core, ())


def diff(S, Tset):
    # subtraction demands proven membership in T: the marks of S remain
    return ZSet(S.core - Tset.core, S.quar)


def card_bounds(S):
    lo = len(S.core) if S.core else (1 if S.quar else 0)
    return (lo, len(S.core) + len(S.quar))


def distinct(S):
    """SQL DISTINCT our way: the core deduplicated classically,
    marks must not be merged (merging is not earned)."""
    return ZSet(S.core, S.quar)


# ---------------------------------------------------------------- measurements
def hdr(t):
    print("\n### " + t)


if __name__ == "__main__":
    print("=" * 72)
    print("E5. SETS WITH UNVERIFIED ELEMENTS")
    print("=" * 72)

    z1, z2 = M_("sensor#1"), M_("sensor#2")
    S_zz = ZSet((), ("sensor#1", "sensor#1"))     # {Z, Z} (the same mark twice)
    S_z = ZSet((), ("sensor#1",))                  # {Z}
    A = ZSet((1, 2), ("m1",))                      # {1, 2, Z}
    CLEAN = ZSet((1, 2))                           # {1, 2}

    hdr("Key reconnaissance questions")
    print(f"  {{Z,Z}} = {{Z}} (verdict): {seteq(S_zz, S_z)}   "
          f"(representation: {S_zz.repr_eq(S_z)}) — merging not earned")
    print(f"  Z ∈ {{Z}} (the same mark!): {mem(M_('sensor#1'), S_z)} — "
          f"membership not earned (SQL: NULL IN (NULL) — not true)")
    print(f"  1 ∈ {{1,2,Z}}: {mem(V_(1), A)}   3 ∈ {{1,2,Z}}: {mem(V_(3), A)}")

    hdr("Set laws: clean versus marked (seteq verdict)")
    laws = [
        ("S ∪ S = S (idempotence)", lambda S: (union(S, S), S)),
        ("S ∩ S = S", lambda S: (intersect(S, S), S)),
        ("S \\ S = ∅", lambda S: (diff(S, S), ZSet())),
        ("S = S (reflexivity)", lambda S: (S, S)),
        ("S ∪ T = T ∪ S (T={2,3})",
         lambda S: (union(S, ZSet((2, 3))), union(ZSet((2, 3)), S))),
    ]
    print(f"  {'law':38s} {'clean':8s} {'marked':8s} {'repr.(marked)'}")
    for name, f in laws:
        l1, r1 = f(CLEAN)
        l2, r2 = f(A)
        print(f"  {name:38s} {seteq(l1, r1):8s} {seteq(l2, r2):8s} "
              f"{l2.repr_eq(r2)}")

    hdr("Inclusion: even S ⊆ S falls on a marked set")
    print(f"  {{1,2}} ⊆ {{1,2}}: {sub(CLEAN, CLEAN)}")
    print(f"  {{1,2,Z}} ⊆ {{1,2,Z}}: {sub(A, A)} — a mark does not provably")
    print("  belong even to its own set (the legacy of Z∉{Z})")

    hdr("Cardinality — an interval only (the exact number is not earned)")
    for nm, S in [("{1,2}", CLEAN), ("{1,2,Z}", A),
                  ("{Z,Z}", S_zz), ("{Z}", S_z)]:
        lo, hi = card_bounds(S)
        verdict = T if lo == hi else F
        print(f"  |{nm}|: [{lo}, {hi}]   verdict \"|S|={hi}\": {verdict}")

    hdr("Comparison with SQL (its famous inconsistency)")
    print("  SQL: NULL = NULL → not true;  NULL IN (NULL) → not true;")
    print("  yet DISTINCT/GROUP BY MERGE the NULLs — equality of values")
    print("  swapped for equality of marks inside one syntax.")
    d = distinct(ZSet((1,), ("a", "b")))
    lo, hi = card_bounds(d)
    print(f"  Our DISTINCT({{1, Z, Z}}): core deduplicated, marks "
          f"{len(d.quar)} — |·| ∈ [{lo},{hi}]; mark merging not earned,")
    print("  SQL's inconsistency is not inherited (marks live separately).")

    hdr("Summary")
    print("  On clean sets — classical set theory cell for cell")
    print("  (C-extension). A mark breaks exactly the identity laws")
    print("  (idempotence, reflexivity, self-subtraction) — the same families")
    print("  that fell in the logic: the sets INHERITED the price list from")
    print("  the tables, not a single rule was postulated separately.")
