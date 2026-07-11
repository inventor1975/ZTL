# -*- coding: utf-8 -*-
"""
A clip of paradoxes for ZTL: the liar, the A/B carousel, the avenger.

Demonstrates the division of labor fixed in SPEC.md:
  * the tables do NOT extinguish the liar (¬ has no fixed point — shown
    by enumeration);
  * the quarantine flag does: Z-sentences are exempted from the Tarski
    schema;
  * the avenger is expressible (detector isZ = ¬(x↔x)) — and the flag
    pays the bill: the content evaluates to T while the sentence is
    denied truth.
"""

from ztl import T, F, Z, VALUES, NOT, OR, XNOR, isZ


def liar_fixed_points():
    """The liar λ ↔ ¬λ: look for a value v with v = ¬v among all three."""
    print("-- THE LIAR: λ asserts ¬λ; we need v(λ) = v(¬λ) --")
    found = []
    for v in VALUES:
        nv = NOT(v)
        mark = "MODEL" if v == nv else "miss"
        print(f"  λ={v}:  ¬λ={nv}   → {mark}")
        if v == nv:
            found.append(v)
    if not found:
        print("  No fixed point — the tables do NOT extinguish the liar (by design).")
        print("  The flag does: λ receives Z and is exempted from the Tarski schema.")
    return found


def liar_revision(steps=6):
    """Manual spin of the carousel: v ← ¬v. The oscillation the flag freezes."""
    print("\n-- REVISION (spinning the liar by hand) --")
    v = F
    trace = [v]
    for _ in range(steps):
        v = NOT(v)
        trace.append(v)
    print("  " + " → ".join(trace) + " → ... (period 2, never stops)")


def carousel():
    """Jourdain's carousel: A ↔ B and B ↔ ¬A. All 9 pairs, including Z."""
    print("\n-- CAROUSEL A/B: we need v(A)=v(B) and v(B)=v(¬A) --")
    models = []
    for a in VALUES:
        for b in VALUES:
            ok1 = (XNOR(a, b) == T)      # "we agree" holds
            ok2 = (XNOR(b, NOT(a)) == T) # "we differ" holds
            if ok1 and ok2:
                models.append((a, b))
            print(f"  A={a} B={b}:  A↔B={XNOR(a, b)}  B↔¬A={XNOR(b, NOT(a))}"
                  + ("   MODEL" if ok1 and ok2 else ""))
    if not models:
        print("  No models even with Z — both vertices go into quarantine by the flag.")
    return models


def revenge():
    """The avenger μ: "μ is false OR μ is quarantined", content = ¬μ ∨ isZ(μ)."""
    print("\n-- THE AVENGER: μ asserts ¬μ ∨ isZ(μ), where isZ(x)=¬(x↔x) --")
    for v in VALUES:
        content = OR(NOT(v), isZ(v))
        verdict = "would coincide" if content == v else "does not coincide"
        print(f"  μ={v}:  content={content}   ({verdict})")
    print("  At μ=Z the content evaluates to T — and the sentence is denied truth:")
    print("  the bill quarantine pays deliberately (SPEC.md, fork 3).")


if __name__ == "__main__":
    liar_fixed_points()
    liar_revision()
    carousel()
    revenge()
