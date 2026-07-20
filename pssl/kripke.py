# -*- coding: utf-8 -*-
"""
kripke — an INDEPENDENT oracle for intuitionistic logic, by a second
method rather than a second implementation.

Why this exists. The IPC oracle used throughout the PSSL legs is a
contraction-free proof search (Dyckhoff's G4ip, `zipc.prove`). It is
calibrated against 27 textbook laws — but every one of those has an
EMPTY premise set, while the PSSL sweeps ask `ipc_derives` with premises
standing. An error in the premise handling would sit exactly in the
uncalibrated part and never show.

Rewriting G4ip a second time would not help: the same author reproduces
the same misunderstanding. So this is the other method — Kripke
semantics, searching for a finite countermodel:

    Γ ⊬ φ   iff   some finite Kripke model has a world forcing all of Γ
                  and not forcing φ

and the two methods are made to agree on every question the legs ask.

THE ASYMMETRY, which is the point and must not be blurred:

  * a countermodel FOUND is a **witness** — it settles ⊬ outright, and it
    can be printed and checked by hand;
  * no countermodel up to size N is **not** a proof of ⊢. It is the
    absence of a refutation we could reach.

So a disagreement of the form "prove says ⊢, semantics exhibits a
countermodel" is a definitive bug report against one of the two. A
disagreement the other way is a request for a bigger N. This file reports
the two kinds separately and never conflates them — the discipline the
whole PSSL work has been failing and re-learning all day.

Semantics (standard, Kripke 1965):
    w ⊨ p       iff  p ∈ L(w)
    w ⊨ A∧B     iff  w ⊨ A and w ⊨ B
    w ⊨ A∨B     iff  w ⊨ A or w ⊨ B
    w ⊨ A→B     iff  for every v ≥ w: v ⊨ A implies v ⊨ B
    w ⊨ ¬A      iff  for every v ≥ w: v ⊭ A
with L monotone along ≤ (persistence).

Models enumerated: every partial order on k ≤ MAXW elements (every poset
has a linear extension, so it is enough to take transitively closed sets
of pairs i<j), with every monotone labelling over the atoms.

Run:  python3 pssl/kripke.py
"""
import itertools
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
sys.path.insert(0, _ROOT)

import zipc                                                   # noqa: E402

MAXW = 4           # worlds; raised in the sweep where it matters
ATOMS = ("p", "q")


# ---------------------------------------------------------------------------
# Models
# ---------------------------------------------------------------------------
def posets(k):
    """Every partial order on {0..k-1}. Every poset has a linear
    extension, so we may assume i ≤ j only when i ≤ j numerically; then a
    poset is a transitively closed subset of the strict pairs."""
    pairs = [(i, j) for i in range(k) for j in range(k) if i < j]
    for bits in itertools.product((0, 1), repeat=len(pairs)):
        rel = {p for p, b in zip(pairs, bits) if b}
        if all((i, m) in rel
               for (i, j) in rel for (l, m) in rel if j == l):
            le = [[False] * k for _ in range(k)]
            for i in range(k):
                le[i][i] = True
            for (i, j) in rel:
                le[i][j] = True
            yield le


def labellings(k, le, atoms):
    """Monotone assignments of atom-sets to worlds (persistence)."""
    for combo in itertools.product(range(1 << len(atoms)), repeat=k):
        if all(not le[i][j] or (combo[i] & combo[j]) == combo[i]
               for i in range(k) for j in range(k)):
            yield [{a for n, a in enumerate(atoms) if combo[w] >> n & 1}
                   for w in range(k)]


def forces(phi, w, le, L, k):
    if isinstance(phi, str):
        return phi in L[w]
    op = phi[0]
    if op == "not":
        return all(not le[w][v] or not forces(phi[1], v, le, L, k)
                   for v in range(k))
    if op == "and":
        return forces(phi[1], w, le, L, k) and forces(phi[2], w, le, L, k)
    if op == "or":
        return forces(phi[1], w, le, L, k) or forces(phi[2], w, le, L, k)
    if op == "imp":
        return all(not le[w][v] or not forces(phi[1], v, le, L, k)
                   or forces(phi[2], v, le, L, k)
                   for v in range(k))
    raise ValueError(op)


def countermodel(premises, conclusion, maxw=MAXW, atoms=ATOMS):
    """A finite Kripke countermodel to Γ ⊨ φ, or None if none of size
    ≤ maxw exists. FOUND is a witness; None is not a proof."""
    for k in range(1, maxw + 1):
        for le in posets(k):
            for L in labellings(k, le, atoms):
                for w in range(k):
                    if all(forces(p, w, le, L, k) for p in premises) \
                       and not forces(conclusion, w, le, L, k):
                        return (k, le, L, w)
    return None


def show_model(cm):
    k, le, L, w = cm
    edges = [f"{i}≤{j}" for i in range(k) for j in range(k)
             if i != j and le[i][j]]
    lab = ", ".join(f"{i}:{{{','.join(sorted(L[i])) or '∅'}}}" for i in range(k))
    return (f"{k} worlds [{lab}]"
            + (f" with {' '.join(edges)}" if edges else " (discrete)")
            + f", refuted at {w}")


# ---------------------------------------------------------------------------
# The cross-check
# ---------------------------------------------------------------------------
def show(phi):
    if isinstance(phi, str):
        return phi
    if phi[0] == "not":
        return f"¬{show(phi[1])}"
    return (f"({show(phi[1])}"
            + {"and": "∧", "or": "∨", "imp": "→"}[phi[0]]
            + f"{show(phi[2])})")


def cross_check(cases, maxw=MAXW, label=""):
    """Returns (agree, bugs, unreached). A `bug` is the definitive kind:
    the prover says derivable and semantics exhibits a countermodel."""
    agree, bugs, unreached = 0, [], []
    for prems, concl in cases:
        proved = zipc.prove(frozenset(zipc.to_ipc(p) for p in prems),
                            zipc.to_ipc(concl))
        cm = countermodel(list(prems), concl, maxw)
        if proved and cm is not None:
            bugs.append((prems, concl, cm))
        elif (not proved) and cm is None:
            unreached.append((prems, concl))
        else:
            agree += 1
    return agree, bugs, unreached


if __name__ == "__main__":
    print("=" * 78)
    print("AN INDEPENDENT IPC ORACLE — Kripke countermodels")
    print("  Second METHOD, not second implementation: rewriting G4ip")
    print("  would reproduce the same misunderstanding twice.")
    print("=" * 78)

    # -------------------------------------------------- 1. calibrate US
    print("\n### 1. Calibrating the SEMANTICS against known facts")
    known = [
        ("p→p",            ("imp", "p", "p"),                       False),
        ("LEM p∨¬p",       ("or", "p", ("not", "p")),               True),
        ("DNE ¬¬p→p",      ("imp", ("not", ("not", "p")), "p"),     True),
        ("DNI p→¬¬p",      ("imp", "p", ("not", ("not", "p"))),     False),
        ("Peirce",         ("imp", ("imp", ("imp", "p", "q"), "p"), "p"), True),
        ("¬(p∧¬p)",        ("not", ("and", "p", ("not", "p"))),     False),
        ("weak LEM",       ("or", ("not", "p"), ("not", ("not", "p"))), True),
        ("Dummett",        ("or", ("imp", "p", "q"), ("imp", "q", "p")), True),
    ]
    bad = 0
    for name, phi, should_refute in known:
        cm = countermodel([], phi)
        ok = (cm is not None) == should_refute
        bad += not ok
        print(f"  [{'OK ' if ok else 'FAIL'}] {name:16s} "
              + (f"countermodel: {show_model(cm)}" if cm
                 else "no countermodel — valid"))
    assert bad == 0, "the semantics itself is miscalibrated"

    # -------------------------------------------------- 2. laws
    print("\n### 2. Cross-check on the 27-law battery (Γ = ∅)")
    a, bugs, un = cross_check([([], f) for _, f, _ in zipc.LAWS])
    print(f"  agree {a} / {len(zipc.LAWS)}   definitive bugs {len(bugs)}"
          f"   unreached-at-N {len(un)}")
    for prems, concl, cm in bugs:
        print(f"    BUG  ⊢ {show(concl)} yet {show_model(cm)}")
    for prems, concl in un:
        print(f"    unreached  ⊬ {show(concl)} but no countermodel ≤ {MAXW}")

    # -------------------------------------------------- 3. THE GAP
    print("\n### 3. THE UNCALIBRATED PART — rules with premises")
    print("  Every one of the 27 laws has Γ = ∅. The PSSL sweeps ask")
    print("  ipc_derives WITH premises, and nothing until now checked")
    print("  that part of the prover against anything.\n")
    a2, bugs2, un2 = cross_check([(list(p), c) for _, p, c in zipc.RULES])
    print(f"  14-rule battery : agree {a2} / {len(zipc.RULES)}"
          f"   bugs {len(bugs2)}   unreached {len(un2)}")
    for prems, concl, cm in bugs2:
        print(f"    BUG  {', '.join(show(p) for p in prems)} ⊢ {show(concl)}"
              f" yet {show_model(cm)}")
    for prems, concl in un2:
        print(f"    unreached  {', '.join(show(p) for p in prems)} ⊬ "
              f"{show(concl)}, no countermodel ≤ {MAXW}")

    # -------------------------------------------------- 4. the real sweep
    print("\n### 4. The generated sweep — every single-premise pair the")
    print("   PSSL legs actually asked of the prover")
    pool = zipc.build_pool(("p", "q"), depth=1)
    cases = [([g], f) for g in pool for f in pool]
    a3, bugs3, un3 = cross_check(cases)
    print(f"  {len(cases)} pairs : agree {a3}   bugs {len(bugs3)}"
          f"   unreached {len(un3)}")
    for prems, concl, cm in bugs3[:5]:
        print(f"    BUG  {show(prems[0])} ⊢ {show(concl)} yet {show_model(cm)}")
    for prems, concl in un3[:5]:
        print(f"    unreached  {show(prems[0])} ⊬ {show(concl)}")

    # -------------------------------------------------- 5. two premises
    print("\n### 5. TWO premises — the shape the deduction-theorem sweep")
    print("   actually used (Γ, γ ⊨ φ with a context standing), and the")
    print("   shape on which apartness separated classical from LP")
    import random
    random.seed(20260720)
    small = pool[:8]
    cases2 = [([a, b], f) for a in small for b in small for f in small]
    a4, bugs4, un4 = cross_check(cases2)
    print(f"  {len(cases2)} triples : agree {a4}   bugs {len(bugs4)}"
          f"   unreached {len(un4)}")
    for prems, concl, cm in bugs4[:5]:
        print(f"    BUG  {', '.join(show(p) for p in prems)} ⊢ {show(concl)}"
              f" yet {show_model(cm)}")
    for prems, concl in un4[:5]:
        print(f"    unreached  {', '.join(show(p) for p in prems)} ⊬ "
              f"{show(concl)}")

    print(f"\n{'=' * 78}\nVERDICT\n{'=' * 78}")
    tb = len(bugs) + len(bugs2) + len(bugs3) + len(bugs4)
    tu = len(un) + len(un2) + len(un3) + len(un4)
    print(f"  definitive bugs (prover says ⊢, model refutes) : {tb}")
    print(f"  unreached at {MAXW} worlds (⊬ with no small model): {tu}")
    print()
    if tb == 0 and tu == 0:
        print("  The two methods agree everywhere they were asked. The")
        print("  premise-handling half of the prover — uncalibrated until")
        print("  now — is corroborated by a semantics that shares no code")
        print("  with it.")
    print("\n  CEILING: 'no countermodel at 4 worlds' is not a proof of")
    print("  derivability. This file settles UNDERIVABILITY with witnesses")
    print("  and corroborates derivability; it does not prove it.")
    assert tb == 0, f"the prover is refuted by a countermodel: {bugs + bugs2 + bugs3}"
    assert tu == 0, f"underivable with no small countermodel: {un + un2 + un3}"
    print("\n  KRIPKE CROSS-CHECK GREEN")
