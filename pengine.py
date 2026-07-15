# -*- coding: utf-8 -*-
"""
pengine — the paradox engine. One operational construction; the whole zoo of
paradoxes is its range.

The seam (curator's intuition, "a paradox IS an operator"):

    paradox(f)  =  ground( S = f(S) )

Feed an operator f (a formula with a hole S for the self-reference), form the
self-referential sentence S = f(S), run the zero-trust grounding (lazy least
fixed point). A paradox is then not a hand-classified specimen — it is the
OUTPUT of this one procedure, parameterised by f:

    Liar = paradox(¬S)   truth-teller = paradox(S)   Curry = paradox(S→⊥)

MEASURED relationship (the engine corrected a tempting-but-false guess).
Naively one hopes "quarantine ⟺ the self-equation S=f(S) has ≠1 classical
solution". FALSE: `S = S∧¬S` has the unique classical solution F, yet grounds
to Z — the grounding starts from ignorance and will not commit to F unless the
operator PULLS it there. So the true, measured facts are:

    * grounded ∈ {Z} ∪ (classical fixed points of f)          — always
    * f has NO classical fixed point   ⟹  Z  (forced)          — over-constrained
    * f HAS classical fixed point(s)   ⟹  Z  OR  grounds       — depends on the
      lazy dynamics from Z; grounding is STRICTER than classical solvability.

(Names here are provisional — to be polished.)
"""

from ztl import T, F, Z, ev
from fixedpoint import least_fp_lazy

HOLE = "S"                                   # the self-reference placeholder


def classical_fixpoints(f):
    """x ∈ {T,F} with f(x)=x — the classical solutions of S=f(S)."""
    return [x for x in (T, F) if ev(f, {HOLE: x}) == x]


def greedy_orbit(f, start, steps=4):
    """The behaviour when you COMMIT: iterate the greedy jump x ↦ f(x)."""
    orbit, x = [start], start
    for _ in range(steps):
        x = ev(f, {HOLE: x})
        orbit.append(x)
    return orbit


def paradox(f):
    """The construction. Returns the grounded verdict, the classical solutions,
    the (measured) kind, and the committing orbit."""
    grounded = least_fp_lazy({HOLE: f})[HOLE]        # zero-trust grounding
    fps = classical_fixpoints(f)
    if grounded != Z:
        kind = f"grounds to {grounded}"
    elif not fps:
        kind = "over-constrained (no classical solution) → Z"
    else:
        kind = ("cautious quarantine: solution {" + ",".join(fps) +
                "} exists, but grounding-from-Z won't reach it → Z")
    return {"grounded": grounded, "fixpoints": fps, "kind": kind,
            "orbit_from_T": greedy_orbit(f, T)}


# the classic specimens, each as ONE instance of paradox(f) --------------------
ZOO = {
    "Liar         S = ¬S":    ("not", HOLE),
    "truth-teller S = S":     HOLE,
    "double-neg   S = ¬¬S":   ("not", ("not", HOLE)),
    "Curry        S = S→⊥":   ("imp", HOLE, "F"),
    "contra       S = S∧¬S":  ("and", HOLE, ("not", HOLE)),
    "grounded-T   S = S∨⊤":   ("or", HOLE, "T"),
    "grounded-F   S = S∧⊥":   ("and", HOLE, "F"),
}


def report_zoo():
    print("THE ZOO AS paradox(f) — one construction, many operators\n")
    for name, f in ZOO.items():
        r = paradox(f)
        z = "  ⟵ QUARANTINE (Z)" if r["grounded"] == Z else ""
        fps = "{" + ",".join(r["fixpoints"]) + "}"
        print(f"  {name}")
        print(f"      grounded = {r['grounded']}{z}   | classical solutions {fps}")
        print(f"      {r['kind']}")
        print(f"      orbit when committed (from T): "
              f"{' → '.join(r['orbit_from_T'])}\n")


def sweep():
    """A finite family; MEASURE the true relationship (no wishful law)."""
    fam = {
        "¬S": ("not", HOLE), "¬¬S": ("not", ("not", HOLE)), "S": HOLE,
        "S∧¬S": ("and", HOLE, ("not", HOLE)),
        "S∨¬S": ("or", HOLE, ("not", HOLE)),
        "S∧⊤": ("and", HOLE, "T"), "S∧⊥": ("and", HOLE, "F"),
        "S∨⊤": ("or", HOLE, "T"), "S∨⊥": ("or", HOLE, "F"),
        "S→⊥": ("imp", HOLE, "F"), "S→⊤": ("imp", HOLE, "T"),
        "⊤→S": ("imp", "T", HOLE), "⊥→S": ("imp", "F", HOLE),
        "S↔⊤": ("xnor", HOLE, "T"),
    }
    print("SWEEP — the measured relationship (grounding is stricter than "
          "classical solvability)\n")
    print(f"  {'f(S)':6s} {'#sol':>4} {'ground':>6}   note")
    inv_ok = True
    for label, f in fam.items():
        fps = classical_fixpoints(f)
        g = least_fp_lazy({HOLE: f})[HOLE]
        inv_ok &= (g == Z or g in fps)                # grounded ∈ {Z}∪fps
        if g == Z and fps:
            note = "CAUTIOUS Z (has a solution, won't commit)"
        elif g == Z:
            note = "forced Z (no solution)"
        else:
            note = f"grounds ({g} is the unique solution reached)"
        print(f"  {label:6s} {len(fps):>4} {g:>6}   {note}")
    print(f"\n  invariant  grounded ∈ {{Z}} ∪ solutions : {inv_ok}")
    print("  → #sol=0 forces Z; #sol≥1 may still be Z (S∧¬S, S∨⊤ vs S↔⊤).")
    print("  → so 'paradoxical' = grounding won't reach a classical value —")
    print("    a fact about the operator's LAZY dynamics, not its solution count.")


if __name__ == "__main__":
    report_zoo()
    print("=" * 64 + "\n")
    sweep()
