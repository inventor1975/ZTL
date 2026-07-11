# -*- coding: utf-8 -*-
"""
Expedition E10: the modal layer of ZTL.

Worlds = classical completions of the unverified atoms. □φ = in all
worlds, ◇φ = in at least one. Measurements:
  1. Atom verdicts = modal thresholds (T⟺□, F⟺□¬, Z⟺contingent) +
     the duality ◇ = ¬□¬ and the S5 collapse (□□=□).
  2. Tableau signs = modal claims: strict T/F = □, P/N = ◇.
  3. Columns: classical | global □ (supervaluation) | ZTL (a local □
     behind every operator) — three different logics on one formula.
Bochvar's translations (our → = ◇A⊃□B) acquire world semantics.
"""

from itertools import product

from ztl import T, F, Z, OPS2, NOT, ev, atoms, all_envs

# ------------------------------------------------- worlds and modalities
def worlds(marked):
    """All classical completions: marked — dict atom → 'V:T'/'V:F'/'M'."""
    names = sorted(marked)
    opts = [[marked[n]] if marked[n] in (T, F) else [T, F] for n in names]
    return [dict(zip(names, combo)) for combo in product(*opts)]


def classical_eval(phi, world):
    return ev(phi, world)          # on classical worlds ev is classical


def box(phi, marked):
    return all(classical_eval(phi, w) == T for w in worlds(marked))


def dia(phi, marked):
    return any(classical_eval(phi, w) == T for w in worlds(marked))


def ztl_eval(phi, marked):
    env = {n: (v if v in (T, F) else Z) for n, v in marked.items()}
    return ev(phi, env)


def global_super(phi, marked):
    """Global supervaluation: one □ over the whole formula."""
    if box(phi, marked):
        return T
    if not dia(phi, marked):
        return F
    return Z                        # super-gap


if __name__ == "__main__":
    print("=" * 72)
    print("E10. THE MODAL LAYER: completion worlds, local □ versus global")
    print("=" * 72)

    p, q = "p", "q"

    print("\n### 1. Atoms: verdicts = modal thresholds (totally)")
    ok = True
    for st in (T, F, "M"):
        marked = {p: st}
        v = ztl_eval(p, marked)
        b, d = box(p, marked), dia(p, marked)
        expect = T if b else (F if not d else Z)
        ok &= (v == expect)
        print(f"  atom p[{'mark' if st == 'M' else st}]: verdict {v},"
              f"  □p={b}, ◇p={d}  → threshold {'coincided' if v == expect else 'DIVERGENCE'}")
    # duality and the S5 collapse
    dual = all(dia(p, {p: st}) == (not box(("not", p), {p: st}))
               for st in (T, F, "M"))
    print(f"  duality ◇p = ¬□¬p: {'✓' if dual else '✗'};"
          f"  □□ = □ trivially (□p is classical) — S5 collapse of nesting")

    print("\n### 2. Tableau signs as modal claims")
    marked = {p: "M"}
    print("  sign T:φ  = □φ   (a strict claim: forced by all completions)")
    print("  sign F:φ  = □¬φ  (a strict refutation)")
    print(f"  sign P:φ = ◇φ:  for a mark ◇p = {dia(p, marked)} — a possibility claim")
    print(f"  sign N:φ = ◇¬φ: for a mark ◇¬p = {dia(('not', p), marked)}")
    print("  \"Weak signs only in F-polarity\" = refutation settles for")
    print("  possibility, proof demands necessity.")

    print("\n### 3. Three logics on the same formulas: classical | global □ | ZTL")
    battery = [
        ("¬¬p",        ("not", ("not", p))),
        ("p → p",      ("imp", p, p)),
        ("p ∨ ¬p",     ("or", p, ("not", p))),
        ("¬(p ∧ ¬p)",  ("not", ("and", p, ("not", p)))),
        ("p ∧ ¬p",     ("and", p, ("not", p))),
        ("(p∧q)→p",    ("imp", ("and", p, q), p)),
    ]
    marked = {p: "M", q: "M"}
    print(f"  {'formula':14s} {'classical(p=T)':14s} {'global □':13s} {'ZTL':4s}")
    for nm, phi in battery:
        cl = classical_eval(phi, {p: T, q: T})
        gs = global_super(phi, marked)
        zt = ztl_eval(phi, marked)
        print(f"  {nm:14s} {cl:14s} {gs:13s} {zt:4s}")
    print("  The global □ (supervaluation) preserves ALL classical")
    print("  tautologies (p→p, LEM — true \"as a whole\" without knowing p);")
    print("  ZTL puts the □ LOCALLY behind every operator — the tautologies")
    print("  of form fall, while ¬¬p conversely earns T (the ladder of floors).")
    print("  The supervaluation/ZTL split = global/local modality.")

    print("\n### Summary")
    print("  ZTL is a locally-modal logic over the S5 frame of completion")
    print("  worlds: every operator carries its own □-collapse. Bochvar's")
    print("  translations (our → = ◇A⊃□B, ¬ = □¬) are its modal notation,")
    print("  now with world semantics. Tableau signs = {□, □¬, ◇, ◇¬}.")
    print("  The theoretical relative: Hintikka's epistemic S5 (□ = \"known\") —")
    print("  ZTL asserts only the known, but its modality is per-operator,")
    print("  not propositional.")
