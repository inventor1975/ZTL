# -*- coding: utf-8 -*-
"""
arrow_control — PSSL leg 2, tack 2a: attacking our own leg-1 result.

Leg 1 concluded that the four grounds split 2/2 by whether they have the
deduction theorem, with quantum MO2 on the "no" side. But leg 1's design
decision D2 handed the quantum corner the **Sasaki hook by declaration**
— an ortholattice has no canonical implication, and we chose one.

So the obvious attack on our own result: **is the failure a property of
MO2, or of our choice of arrow?** If some other implication restores the
deduction theorem, the quantum half of the 2/2 split is an artefact of a
declaration we made, and leg 1 must say so where it says the result.

This is checked first, deliberately. If we do not run it, a referee runs
it, and then it is their finding rather than ours.

THE ARROWS. Every implication proposed for orthomodular lattices in the
literature (Kalmbach's five, plus the material one for contrast). Each is
classical on a Boolean algebra — that is the standard requirement — and
they differ only off the diagonal:

  material    ¬x ∨ y
  Sasaki      ¬x ∨ (x ∧ y)                      (leg 1's declaration)
  Dishkant    y ∨ (¬y ∧ ¬x)                     (the Sasaki dual)
  Kalmbach    (¬x∧y) ∨ (¬x∧¬y) ∨ (x∧(¬x∨y))
  non-tollens (¬x∧y) ∨ (x∧y) ∨ ((¬x∨y)∧¬y)
  relevance   (¬x∧y) ∨ (¬x∧¬y) ∨ (x∧y)

MEASURED (this file, deterministic, MO2 = 6 elements, 216 triples):
  see the table printed by the run — the answer is not asserted here in
  prose, because the whole point of the tack is that we did not know it.

Run:  python3 pssl/arrow_control.py
"""
import itertools
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
sys.path.insert(0, os.path.join(_ROOT, "dilemmas"))

import quantum_ladder as QL                                   # noqa: E402

E = QL.ELS
neg, meet, join, leq = QL.NEG, QL.meet, QL.join, QL.leq


# ---------------------------------------------------------------------------
# The candidate arrows
# ---------------------------------------------------------------------------
def a_material(x, y):
    return join(neg[x], y)


def a_sasaki(x, y):
    return join(neg[x], meet(x, y))


def a_dishkant(x, y):
    return join(y, meet(neg[y], neg[x]))


def a_kalmbach(x, y):
    return join(join(meet(neg[x], y), meet(neg[x], neg[y])),
                meet(x, join(neg[x], y)))


def a_non_tollens(x, y):
    return join(join(meet(neg[x], y), meet(x, y)),
                meet(join(neg[x], y), neg[y]))


def a_relevance(x, y):
    return join(join(meet(neg[x], y), meet(neg[x], neg[y])), meet(x, y))


ARROWS = [
    ("material",    a_material),
    ("Sasaki",      a_sasaki),
    ("Dishkant",    a_dishkant),
    ("Kalmbach",    a_kalmbach),
    ("non-tollens", a_non_tollens),
    ("relevance",   a_relevance),
]


# ---------------------------------------------------------------------------
# The three properties that matter for leg 1's claim
# ---------------------------------------------------------------------------
def classical_on_booleans(imp):
    """Sanity: on the Boolean sublattice {bot, a, a', top} every proposed
    arrow must agree with the material one, or it is not an implication
    at all and its verdict below is meaningless."""
    B = ["bot", "a", "a1", "top"]
    return all(imp(x, y) == a_material(x, y)
               for x, y in itertools.product(B, repeat=2)
               if meet(x, y) in B and join(x, y) in B)


def modus_ponens(imp):
    """x ∧ (x → y) ≤ y — the rule must survive, or the arrow is useless."""
    return all(leq(meet(x, imp(x, y)), y)
               for x, y in itertools.product(E, repeat=2))


def deduction_theorem(imp):
    """a ∧ b ≤ c  ⟺  a ≤ (b → c). Returns (holds, failures out of 216).

    The real statement: the discharged premise crosses the arrow while
    the rest of the context stays on the left. Leg 1 spent three passes
    learning that the convenient forms are blind here."""
    bad = [(x, y, z) for x, y, z in itertools.product(E, repeat=3)
           if leq(meet(x, y), z) != leq(x, imp(y, z))]
    return (not bad), len(bad), (bad[0] if bad else None)


def import_export_one_way(imp):
    """The weaker half — a ∧ b ≤ c ⟹ a ≤ (b → c). If even this fails the
    ground cannot discharge at all; if only this holds, it discharges but
    does not re-import."""
    return all(leq(x, imp(y, z))
               for x, y, z in itertools.product(E, repeat=3)
               if leq(meet(x, y), z))


def relative_pseudocomplement_missing():
    """The survey above is unnecessary, and this is why.

    DT says a ≤ (b→c) ⟺ a∧b ≤ c — i.e. `b→c` must BE the greatest x with
    x∧b ≤ c. That is a relative pseudocomplement; a lattice having one
    for every pair is a Heyting algebra, hence distributive. MO2 is not.
    So NO binary operation on MO2 satisfies DT, and no choice of arrow
    could have hidden the failure.

    Machine-checked in `lean/QuantumWitness.lean` as
    `no_arrow_has_deduction_theorem`, empty axiom list."""
    out = []
    for b, c in itertools.product(E, repeat=2):
        S = [x for x in E if leq(meet(x, b), c)]
        if not any(all(leq(y, x) for y in S) for x in S):
            mx = [x for x in S if not any(x != y and leq(x, y) for y in S)]
            out.append((b, c, S, mx))
    return out


if __name__ == "__main__":
    print("=" * 78)
    print("LEG 2, TACK 2a — THE ARROW CONTROL")
    print("  Q1 (pre-registered): the MO2 deduction-theorem failure")
    print("  SURVIVES the change of arrow — it is orthomodularity, not")
    print("  the Sasaki hook we declared in leg 1's decision D2.")
    print("=" * 78)
    print(f"\n  {'arrow':14s}{'classical?':>12s}{'MP?':>7s}"
          f"{'DT?':>7s}{'DT fails':>10s}   first failure")
    results = {}
    for name, imp in ARROWS:
        cls = classical_on_booleans(imp)
        mp = modus_ponens(imp)
        dt, nbad, first = deduction_theorem(imp)
        results[name] = (cls, mp, dt, nbad)
        fw = (f"a={first[0]}, b={first[1]}, c={first[2]}" if first else "—")
        print(f"  {name:14s}{'yes' if cls else 'NO':>12s}"
              f"{'yes' if mp else 'no':>7s}{'yes' if dt else 'no':>7s}"
              f"{nbad:>10d}   {fw}")

    print(f"\n{'=' * 78}\nVERDICT ON Q1\n{'=' * 78}")
    usable = [n for n, (cls, mp, _, _) in results.items() if cls and mp]
    with_dt = [n for n in usable if results[n][2]]
    print(f"  arrows that are classical on Booleans AND keep modus ponens:")
    print(f"    {', '.join(usable) if usable else '(none)'}")
    print(f"  of those, arrows that RESTORE the deduction theorem:")
    print(f"    {', '.join(with_dt) if with_dt else '(none)'}")
    q1 = not with_dt
    print()
    if q1:
        print("  Q1 HOLDS. No usable arrow restores it: the failure belongs")
        print("  to the lattice, not to leg 1's declaration. The quantum")
        print("  half of the 2/2 split stands.")
    else:
        print("  Q1 FAILS. An arrow restores the deduction theorem, so the")
        print("  quantum half of leg 1's split is an artefact of decision")
        print("  D2 — our declaration, not MO2. This must be written into")
        print("  leg 1's results where the result is stated, not in a")
        print("  footnote.")
    assert usable, "no candidate arrow is even a usable implication"
    assert q1, "Q1 flipped — an arrow restored the deduction theorem"

    print(f"\n{'=' * 78}\nAND THE SURVEY WAS UNNECESSARY\n{'=' * 78}")
    miss = relative_pseudocomplement_missing()
    print("  DT requires b→c to BE the greatest x with x∧b ≤ c — a relative")
    print("  pseudocomplement. A lattice with one for every pair is a")
    print("  Heyting algebra, hence distributive; MO2 is not.\n")
    print(f"  pairs (b,c) checked                 : {len(E) ** 2}")
    print(f"  pairs whose set has NO maximum      : {len(miss)}")
    b, c, S, mx = miss[0]
    print(f"  first: b={b}, c={c}   set={S}")
    print(f"         incomparable maximal elements: {mx}")
    print("\n  So NO binary operation on MO2 satisfies the deduction")
    print("  theorem. Not six arrows failing — none can succeed.")
    print("  Machine-checked: lean/QuantumWitness.lean,")
    print("  `no_arrow_has_deduction_theorem`, empty axiom list.")
    assert miss, "a relative pseudocomplement appeared — MO2 changed"
    print("\n  TACK 2a GREEN — Q1 asserted, and upgraded to impossibility.")
