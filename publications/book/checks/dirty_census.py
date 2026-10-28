# -*- coding: utf-8 -*-
"""Greedy judge vs the DIRTY reading (2026-10-25).

The dirty reading (the curator): Z is not ours, its owner may change it between two
reads, so EACH OCCURRENCE is read on its own. As a semantics: rename every occurrence
of a Z-marked atom apart, and call a formula earned iff it is true under every
classical reading of those occurrences.

PREDICTION, frozen before the run:
  P1  "losses" against the dirty reading are ZERO: whenever every occurrence-reading
      is true, the greedy judge says T. (Hunch: a read-once formula is never constant.)
  P2  "leaks" against the dirty reading equal the leaks against the patient judge or
      more: cleaning is a special reading (all occurrences equal), so any revisable
      greedy T is also not earned under occurrences.
Cut-off: one P1 exception and the book does NOT say "against dirty, nothing is lost"."""
import os, sys, itertools, random, collections
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))))  # repo root (moved to publications/book/checks 2026-10-25)
from ztl import T, F, Z, ev
from ztljudge import _show

OPS2 = ("and", "or", "imp", "xor", "xnor")


def apart(phi, m, ctr):
    """Rename every occurrence of a Z-marked atom to a fresh name."""
    if isinstance(phi, str):
        if m[phi] == Z:
            ctr[0] += 1
            return f"{phi}#{ctr[0]}"
        return phi
    return (phi[0],) + tuple(apart(s, m, ctr) for s in phi[1:])


def audit(phi, m):
    if not any(m[a] == Z for a in m):
        return None
    ctr = [0]
    psi = apart(phi, m, ctr)
    names = sorted({x for x in _atoms(psi) if "#" in x})
    if len(names) > 14:                       # 2^14 readings cap; counted, not hidden
        return "skip"
    base = {a: v for a, v in m.items() if v != Z}
    dirty_all_true = all(
        ev(psi, {**base, **dict(zip(names, vs))}) == T
        for vs in itertools.product((T, F), repeat=len(names)))
    marks = [a for a in m if m[a] == Z]
    clean_all_true = all(
        ev(phi, {**m, **dict(zip(marks, vs))}) == T
        for vs in itertools.product((T, F), repeat=len(marks)))
    g = ev(phi, m)
    return g, dirty_all_true, clean_all_true


def _atoms(phi):
    if isinstance(phi, str):
        yield phi
    else:
        for s in phi[1:]:
            yield from _atoms(s)


def run(name, pairs):
    n = collections.Counter(); wit = []
    for phi, m in pairs:
        r = audit(phi, m)
        if r is None:
            continue
        if r == "skip":
            n["skipped_>14_occurrences"] += 1; continue
        g, dirty, clean = r
        n["cells"] += 1
        if dirty and g != T:
            n["loss_vs_dirty"] += 1
            if len(wit) < 4: wit.append((_show(phi), dict(m)))
        if g == T and not dirty: n["leak_vs_dirty"] += 1
        if clean and g != T: n["loss_vs_patient"] += 1
        if clean and g != T and not dirty: n["patient_only_yes"] += 1
        if g == T and not clean: n["leak_vs_patient"] += 1
    print(f"\n  {name}")
    print(f"    marked cells                         {n['cells']}")
    print(f"    skipped (>14 dirty occurrences)      {n['skipped_>14_occurrences']}")
    print(f"    LOSS vs dirty (P1 requires 0)        {n['loss_vs_dirty']}")
    print(f"    loss vs patient (old 'losses')       {n['loss_vs_patient']}")
    print(f"      of them: dirty does NOT earn it    {n['patient_only_yes']}")
    print(f"    leak vs dirty                        {n['leak_vs_dirty']}")
    print(f"    leak vs patient (old 'leaks')        {n['leak_vs_patient']}")
    for w in wit:
        print(f"    EXCEPTION: {w[0]}  {w[1]}")
    return n["loss_vs_dirty"]


A = ("p", "q", "r")
d0 = list(A)
d1 = [("not", a) for a in d0] + [(o, a, b) for o in OPS2 for a in d0 for b in d0]
base = d0 + d1
d2 = [("not", f) for f in d1] + [(o, a, b) for o in OPS2 for a in base for b in base]
pool, seen = [], set()
for f in d0 + d1 + d2:
    if f not in seen:
        seen.add(f); pool.append(f)
print(f"A: {len(pool)} formulas x {3**len(A)} markings")
bad = run("A. exhaustive, depth<=2, three atoms",
          ((f, dict(zip(A, c))) for f in pool
           for c in itertools.product((T, F, Z), repeat=len(A))))

B = ("p", "q", "r", "s")
rnd = random.Random(20261025)
def grow(d):
    if d == 0 or rnd.random() < 0.2: return rnd.choice(B)
    if rnd.random() < 0.25: return ("not", grow(d - 1))
    return (rnd.choice(OPS2), grow(d - 1), grow(d - 1))
bad += run("B. random, depth<=6, four atoms",
           [(grow(6), {a: rnd.choice((T, F, Z)) for a in B}) for _ in range(20000)])

print("\nP1 HOLDS — against the dirty reading the greedy judge loses nothing" if bad == 0
      else f"\nP1 REFUTED — {bad} exceptions")
