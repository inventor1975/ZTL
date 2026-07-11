# -*- coding: utf-8 -*-
"""
Expedition E6: the reals and uncountability through unearned identity.

Objects of two presentations:
  * STREAM — a real-in-the-making: a function i ↦ digit; at time t a
    prefix of length t is verified. Stream equality is an atom:
    prefixes diverged → F (apartness earned by a finite witness);
    they agree up to t → Z (not earned). T IS NEVER EARNED.
  * PRESENTATION — a finitely-presented object (a fraction p/q):
    equality decides finitely → a T/F atom, classical.

Membership/registries — the same ∃-folds as in zsets.py (core tables).

The curator's hypothesis: "the uncountability of ℝ will fit into Z".
The measurements show the exact shape of the answer: Z catches
NON-REGISTRABILITY (a property of presentation), while Cantor's
diagonal adds a separate CARDINALITY failure — classically these two
different impossibilities are merged, here they split.
"""

from fractions import Fraction

from ztl import T, F, Z, OPS2, NOT

OR, AND = OPS2["or"], OPS2["and"]


# ------------------------------------------------------------- streams
def stream_of_fraction(fr, base=10):
    """The stream of decimal digits of a fraction (deterministic, but
    presented ONLY extensionally — digit by digit)."""
    def digit(i):
        return int(fr * base ** (i + 1)) % base
    return digit


def eq_stream_at(x, y, t):
    """Stream-equality atom at time t: F/Z (T is never earned)."""
    for i in range(t):
        if x(i) != y(i):
            return F          # apartness earned by witness i
    return Z                  # agreement up to t — identity not earned


def mem_stream_at(x, registry, t):
    """x ∈ registry (verdict at time t): an ∃-fold of atoms through the tables."""
    v = F
    for y in registry:
        v = OR(v, eq_stream_at(x, y, t))
    return v


def apart_time(x, y, t_max=200):
    """The time by which apartness is earned (or None)."""
    for i in range(t_max):
        if x(i) != y(i):
            return i + 1
    return None


def diagonal(registry, base=10):
    """Cantor's diagonal: against the i-th entry, flip its i-th digit."""
    def digit(i):
        if i < len(registry):
            return (registry[i](i) + 1) % base
        return 0
    return digit


# --------------------------------------------- finite presentations (ℚ)
def eq_pres(a, b):
    """Equality of presentations p/q — a classical atom (decided finitely)."""
    return T if a == b else F


def mem_pres(x, registry):
    v = F
    for y in registry:
        v = OR(v, eq_pres(x, y))
    return v


# ---------------------------------------------------------------- measurements
if __name__ == "__main__":
    print("=" * 72)
    print("E6. THE REALS: UNEARNED IDENTITY AND TWO ENUMERATION FAILURES")
    print("=" * 72)

    fr = [Fraction(1, 3), Fraction(1, 7), Fraction(22, 7) % 1,
          Fraction(1, 3)]                      # the last = a duplicate of the first!
    R = [stream_of_fraction(f) for f in fr]    # a registry of four streams

    print("\n### The fate of the stream-equality atom (t = 5, 20, 100)")
    pairs = [("R0 versus R1 (1/3 vs 1/7)", R[0], R[1]),
             ("R0 versus R3 (1/3 vs 1/3 — DUPLICATE)", R[0], R[3]),
             ("R0 versus itself", R[0], R[0])]
    for name, a, b in pairs:
        vals = [eq_stream_at(a, b, t) for t in (5, 20, 100)]
        print(f"  {name:42s} {' '.join(vals)}")
    print("  Different — F (apartness earned); agreeing — eternal Z:")
    print("  T is not earned at ANY t — the comparison is infinite.")

    print("\n### Failure #1 (zero-trust): the registry certifies NO ONE")
    for t in (5, 20, 100):
        verdicts = [mem_stream_at(x, R, t) for x in R]
        print(f"  t={t:3d}: membership of each of R in R itself: "
              f"{' '.join(verdicts)}")
    print("  Even streams literally standing in the list (including the")
    print("  duplicate!) earn no membership: the ∃-fold over {F, Z} gives F.")
    print("  An enumeration of streams cannot CERTIFY coverage of a single element.")

    print("\n### Failure #2 (Cantorian): the diagonal earns apartness")
    d = diagonal(R)
    for i, y in enumerate(R):
        ta = apart_time(d, y)
        print(f"  diagonal versus R{i}: apartness earned by t={ta}")
    print(f"  membership of the diagonal in R (t=100): {mem_stream_at(d, R, 100)}")
    print("  The diagonal is not merely outside the list — its non-membership")
    print("  is EARNED by finite witnesses against every entry.")

    print("\n### Contrast: finitely-presented objects (ℚ as fractions) register")
    Q = [Fraction(1, 3), Fraction(1, 7), Fraction(22, 7) % 1]
    for q in Q + [Fraction(2, 5)]:
        print(f"  {str(q):6s} ∈ the fraction registry: {mem_pres(q, Q)}")
    print("  A presentation decides equality finitely → T/F atoms → the registry")
    print("  certifies each of its elements. The countability of ℚ is the")
    print("  EARNABILITY OF PRESENTATION IDENTITY, not a fact about magnitude.")

    print("\n### Summary (the shape of the answer to the hypothesis)")
    print("  Uncountability split into TWO different impossibilities:")
    print("  1) NON-REGISTRABILITY — zero-trust, about presentation:")
    print("     extensional streams earn no identity, hence no registry")
    print("     certifies a single row (not even its own).")
    print("  2) INCOMPLETENESS — Cantorian, about cardinality: the diagonal")
    print("     earns finite witnesses against every entry.")
    print("  Classical usage merges them into the one word \"uncountable\";")
    print("  the Z-optics splits them — and #1 indeed \"fit into Z\" entirely.")
