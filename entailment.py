# -*- coding: utf-8 -*-
"""
The "keel" stage: the ZTL entailment relation.

    Γ ⊨ φ  ⟺  every value assignment making ALL premises T makes the
              conclusion T as well (the only designated value is T).

Properties that are Tarskian BY CONSTRUCTION (the proof is the shape of
the definition, not enumeration):
  * reflexivity: φ ∈ Γ ⇒ Γ ⊨ φ;
  * monotonicity: Γ ⊨ φ ⇒ Γ∪Δ ⊨ φ (more premises — fewer assignments);
  * cut: Γ ⊨ ψ and Γ,ψ ⊨ φ ⇒ Γ ⊨ φ.

What is measured by enumeration (MEASURED):
  1. The deduction theorem: A ⊨ B versus ⊨ A→B — the arrow is stricter
     than entailment.
  2. The battery of classical RULES as entailments — what survived.
  3. Paracompleteness: no gluts (p,¬p unattainable together), explosion
     vacuously valid; ZTL is paracomplete, NOT paraconsistent in the
     ⊨ sense.
"""

from ztl import T, F, Z, ev, atoms, all_envs, show


def entails(premises, conclusion):
    """None if Γ ⊨ φ; otherwise the first counterexample (assignment)."""
    names = atoms(conclusion, set())
    for prem in premises:
        atoms(prem, names)
    for env in all_envs(names):
        if all(ev(p, env) == T for p in premises) and ev(conclusion, env) != T:
            return env
    return None


def fmt_env(env):
    return ", ".join(f"{k}={v}" for k, v in sorted(env.items())) or "(empty)"


p, q, r = "p", "q", "r"

RULES = [
    # (name, premises, conclusion) — all classically valid
    ("modus ponens         p, p→q ⊨ q",        [p, ("imp", p, q)], q),
    ("modus tollens        p→q, ¬q ⊨ ¬p",      [("imp", p, q), ("not", q)], ("not", p)),
    ("contraposition-rule  p→q ⊨ ¬q→¬p",       [("imp", p, q)], ("imp", ("not", q), ("not", p))),
    ("disjunctive syllogism p∨q, ¬p ⊨ q",      [("or", p, q), ("not", p)], q),
    ("∧-introduction       p, q ⊨ p∧q",        [p, q], ("and", p, q)),
    ("∧-elimination        p∧q ⊨ p",           [("and", p, q)], p),
    ("∨-introduction       p ⊨ p∨q",           [p], ("or", p, q)),
    ("¬¬-introduction      p ⊨ ¬¬p",           [p], ("not", ("not", p))),
    ("¬¬-elimination       ¬¬p ⊨ p",           [("not", ("not", p))], p),
    ("transitivity         p→q, q→r ⊨ p→r",    [("imp", p, q), ("imp", q, r)], ("imp", p, r)),
    ("monotonicity-K       q ⊨ p→q",           [q], ("imp", p, q)),
    ("tautology in concl.  p ⊨ q∨¬q",          [p], ("or", q, ("not", q))),
    ("explosion            p, ¬p ⊨ q",         [p, ("not", p)], q),
    ("resolution           p∨q, ¬p∨r ⊨ q∨r",   [("or", p, q), ("or", ("not", p), r)], ("or", q, r)),
]


def run_rules():
    print("-- BATTERY OF CLASSICAL RULES AS ENTAILMENTS --")
    alive = dead = 0
    for name, prems, concl in RULES:
        cex = entails(prems, concl)
        if cex is None:
            print(f"  ✓ {name}")
            alive += 1
        else:
            print(f"  ✗ {name}   [counterexample: {fmt_env(cex)}]")
            dead += 1
    print(f"  Rules total: alive {alive}, fallen {dead}.")


def run_deduction_theorem():
    print("\n-- DEDUCTION THEOREM: A ⊨ B versus ⊨ A→B --")
    pool = [p, ("not", p), ("and", p, q), ("or", p, q), ("imp", p, q), q]
    mismatch = []
    for A in pool:
        for B in pool:
            rule = entails([A], B) is None          # A ⊨ B
            law = entails([], ("imp", A, B)) is None  # ⊨ A→B
            if rule != law:
                mismatch.append((A, B, rule, law))
    # the →-elimination direction: ⊨A→B ⇒ A⊨B (must hold — semantic MP)
    broken_elim = [(A, B) for A, B, rule, law in mismatch if law and not rule]
    print(f"  Pairs with divergence: {len(mismatch)}; "
          f"of them ⊨A→B without A⊨B: {len(broken_elim)} (must be 0)")
    for A, B, rule, law in mismatch[:4]:
        print(f"    {show(A)} ⊨ {show(B)}: {'yes' if rule else 'no'};   "
              f"⊨ {show(('imp', A, B))}: {'yes' if law else 'no'}")
    print("  Diagnosis: the arrow is STRICTER than entailment — →-introduction")
    print("  fails, →-elimination works. Deduction theorem: left-to-right only.")


def run_paracomplete():
    print("\n-- PARACOMPLETENESS, NOT PARACONSISTENCY --")
    both = [env for env in all_envs({"p"})
            if ev(p, env) == T and ev(("not", p), env) == T]
    print(f"  Assignments with v(p)=v(¬p)=T: {len(both)} — no gluts,")
    print("  explosion p,¬p ⊨ q is vacuously valid (see the battery).")
    lem = entails([], ("or", p, ("not", p)))
    print(f"  LEM ⊭ (counterexample {fmt_env(lem)}) — gaps exist.")
    print("  Verdict: ZTL is paracomplete (truth not everywhere); it is not")
    print("  paraconsistent in the ⊨ sense: contradiction is inexpressible as a pair of truths.")


if __name__ == "__main__":
    print("=" * 72)
    print("THE KEEL: ZTL ENTAILMENT RELATION (designated value {T})")
    print("=" * 72)
    run_rules()
    run_deduction_theorem()
    run_paracomplete()
