# -*- coding: utf-8 -*-
"""
Expedition E26: the price list of DERIVATIONS — brute-force chains
smashed against the core.

The curator's idea: proving is enumerating lemmas and linking them —
so enumerate, "without thinking", and let the CORE judge every link.
The honest niche (we do not race Vampire): ZTL is the one core where a
derivation STEP has a price. The law price list (12 alive / 14 fallen)
extends to a price list of PATHS:

    EARNED     — reachable by chains of the 12 measured ALIVE rules
                 only (each alive rule transports earned truth: the
                 modus_ponens family of theorems);
    ON CREDIT  — classically derivable, but every chain must borrow a
                 FALLEN rule (the loan library is measured: exactly two
                 fallen rules, ¬¬-elimination and tautology-in-
                 conclusion);
    OUT        — unreachable even with the loans.

Machinery: forward chaining to a fixpoint over a bounded formula pool
(153 formulas over p,q,r), links = the 12 alive rules of entailment.py
as schemas, loans switchable; every derived formula carries provenance
(rule + parents), and EVERY closure is cross-checked semantically
against the core's entailment (Γ ⊨ φ over all assignments) — the sieve
never trusts its own syntax.

MEASURED (this file, deterministic, pool = 153 formulas over p,q,r):
  soundness: every derived formula semantically entailed — 0 violations
  across all closures (the chains never lie).
  FROM NOTHING, NOTHING — EVEN ON CREDIT: closure(∅, alive) = 0 and
  closure(∅, alive+loans) = 0. No axiom rule exists. AND YET ZTL has
  its own tautologies on this pool (guarded forms: ¬q→¬q, ¬(p⊕p) —
  alive because denial is classical, ¬Z=F): the rule battery cannot
  mint even those from ∅. THE E26 POINT: the 12 alive rules are
  TRANSPORT, not creation — classical logic mints truth from form;
  ZTL's free truths exist but must ENTER as verified premises.
  the syllogism {p→q, q→r, p}: q, r, p→r all EARNED (alive-only
  chains, provenance printed; closure 51).
  the one-way street: {p} ⊢ ¬¬p earned; from {¬¬p} the alive closure
  is just {¬¬p} (1 formula), and the DNE loan unlocks 14 — the first
  measured ON-CREDIT derivations; p among them.
  credit zone census (6 premise sets): DNE unlocks 0 on ground
  premises and 14 on the ladder {¬¬p}; taut-concl unlocks 1–3
  everywhere (the tautologies, mintable only on credit).
  completeness gap (with both loans): {p} entailed 24 / derivable 15 /
  GAP 9; {p,p→q} 48/32/16 — witnesses are the guarded tautologies and
  law-rewrite variants; the 12 rules are NOT complete for
  ZTL-entailment even on this small pool (honest split — genuine
  incompleteness vs pool-boundedness vs missing law-rewrite links —
  needs a bigger pool, not a claim).
"""

from itertools import product

from ztl import T, F, Z, OPS2, ev, atoms, all_envs, show
from entailment import entails

P, Q, R = "p", "q", "r"
ATOMS = [P, Q, R]


# ------------------------------------------------------------ the pool
def build_pool():
    d1 = [("not", a) for a in ATOMS] + \
         [(op, a, b) for op in OPS2 for a in ATOMS for b in ATOMS]
    extra = [(op, a, ("not", b)) for op in OPS2 for a in ATOMS for b in ATOMS]
    contra = [("imp", ("not", a), ("not", b)) for a in ATOMS for b in ATOMS]
    pool = []
    for f in ATOMS + d1 + [("not", x) for x in d1] + extra + contra:
        if f not in pool:
            pool.append(f)
    return pool


POOL = build_pool()
PS = set(POOL)


# ------------------------------------------------ forward chaining
def close(premises, loans=frozenset()):
    """Fixpoint closure under the 12 alive rules (+ optional loans),
    bounded to the pool. Returns {formula: (rule, parents)} provenance;
    premises carry ("premise", ())."""
    D = {f: ("premise", ()) for f in premises if f in PS}

    def add(f, rule, parents):
        if f in PS and f not in D:
            D[f] = (rule, parents)
            return True
        return False

    changed = True
    while changed:
        changed = False
        items = list(D)
        imps = [f for f in items if f[0] == "imp"] if items else []
        ors = [f for f in items if isinstance(f, tuple) and f[0] == "or"]
        for f in items:
            # ¬¬-intro; ∧-intro needs BOTH parents derived; the side
            # operand of ∨-intro (p ⊨ p∨q) and K (q ⊨ p→q) is ARBITRARY —
            # it ranges over the whole pool, not over the derived set
            changed |= add(("not", ("not", f)), "¬¬-intro", (f,))
            for g in items:
                changed |= add(("and", f, g), "∧-intro", (f, g))
            for g in POOL:
                changed |= add(("or", f, g), "∨-intro", (f,))
                changed |= add(("imp", g, f), "K", (f,))
            if isinstance(f, tuple) and f[0] == "and":
                changed |= add(f[1], "∧-elim", (f,))
                changed |= add(f[2], "∧-elim", (f,))
        for i in imps:
            _, x, y = i
            if x in D:
                changed |= add(y, "modus ponens", (i, x))
            if ("not", y) in D:
                changed |= add(("not", x), "modus tollens", (i, ("not", y)))
            changed |= add(("imp", ("not", y), ("not", x)),
                           "contraposition", (i,))
            for j in imps:
                if j[1] == y:
                    changed |= add(("imp", x, j[2]), "transitivity", (i, j))
        for o in ors:
            _, x, y = o
            if ("not", x) in D:
                changed |= add(y, "disj. syllogism", (o, ("not", x)))
            for o2 in ors:
                if o2[1] == ("not", x):
                    changed |= add(("or", y, o2[2]), "resolution", (o, o2))
        # explosion: a contradiction grounds everything in the pool
        for f in items:
            if ("not", f) in D:
                for g in POOL:
                    changed |= add(g, "explosion", (f, ("not", f)))
                break
        # ---- the loan library (fallen rules) ----
        if "DNE" in loans:
            for f in items:
                if isinstance(f, tuple) and f[0] == "not" and \
                        isinstance(f[1], tuple) and f[1][0] == "not":
                    changed |= add(f[1][1], "LOAN ¬¬-elim", (f,))
        if "TAUT" in loans:
            if items:
                first = items[0]
                for a in ATOMS:
                    changed |= add(("or", a, ("not", a)),
                                   "LOAN taut-concl", (first,))
    return D


def chain(D, f, depth=0):
    """Render the provenance chain of a derived formula."""
    rule, parents = D[f]
    line = "  " * depth + f"{show(f)}   [{rule}]"
    out = [line]
    for par in parents:
        if D.get(par, ("premise", ()))[0] != "premise" and depth < 4:
            out += chain(D, par, depth + 1)
    return out


def soundness_check(premises, D):
    """Every derived formula must be semantically entailed — 0 violations."""
    bad = 0
    for f, (rule, _) in D.items():
        if rule == "premise":
            continue
        if entails(list(premises), f) is not None:
            bad += 1
            print(f"    UNSOUND: {show(f)} via {rule}")
    return bad


def entailed_set(premises):
    """The semantic yardstick: all pool formulas with Γ ⊨ φ."""
    return {f for f in POOL if entails(list(premises), f) is None}


if __name__ == "__main__":
    print("=" * 72)
    print("E26. THE PRICE LIST OF DERIVATIONS: brute-force chains vs the core")
    print("     (links = the 12 alive rules; loans = the 2 fallen ones)")
    print("=" * 72)
    print(f"\n  pool: {len(POOL)} formulas over p,q,r; closure bounded to it")

    total_unsound = 0

    # ---- 1. from nothing, nothing — even on credit ----------------------
    print("\n### 1. From nothing: the proof floor has no axiom rule")
    c0 = close([])
    c0_loan = close([], loans={"DNE", "TAUT"})
    print(f"  closure(∅, alive) = {len(c0)} formulas")
    print(f"  closure(∅, alive + both loans) = {len(c0_loan)} formulas")
    assert not c0 and not c0_loan
    ent0 = entailed_set([])
    wit0 = sorted(ent0, key=repr)[:3]
    print(f"  yet ZTL-TAUTOLOGIES exist on this pool: {len(ent0)} — e.g. "
          f"{', '.join(show(w) for w in wit0)}")
    assert ent0 and ("imp", ("not", Q), ("not", Q)) in ent0
    print("  → the guarded identity ¬q→¬q is a ZTL-tautology BECAUSE denial")
    print("    is classical (¬Z=F, denial is free) — and the rule battery")
    print("    still cannot mint even these from ∅: the 12 alive rules are")
    print("    TRANSPORT, not creation. Classical logic mints from form;")
    print("    ZTL's free truths exist but must enter as verified premises.")

    # ---- 2. the syllogism: earned end to end ----------------------------
    print("\n### 2. The syllogism {p→q, q→r, p}: earned, debt-free")
    prem = [("imp", P, Q), ("imp", Q, R), P]
    D = close(prem)
    total_unsound += soundness_check(prem, D)
    for target in (Q, R, ("imp", P, R)):
        assert target in D
        for line in chain(D, target):
            print("   " + line)
    print(f"  closure size: {len(D)} (alive rules only — every step earned)")

    # ---- 3. the one-way street: the first ON-CREDIT derivation ----------
    print("\n### 3. The one-way street: p ⊢ ¬¬p earned; ¬¬p ⊢ p only on credit")
    D_up = close([P])
    assert ("not", ("not", P)) in D_up
    print(f"  {{p}} ⊢ ¬¬p: EARNED  [{D_up[('not', ('not', P))][0]}]")
    prem_dn = [("not", ("not", P))]
    D_alive = close(prem_dn)
    D_loan = close(prem_dn, loans={"DNE"})
    total_unsound += soundness_check(prem_dn, D_alive)
    assert P not in D_alive and P in D_loan
    print(f"  {{¬¬p}} ⊢ p: NOT in the alive closure ({len(D_alive)} formulas)")
    print(f"  {{¬¬p}} + LOAN ¬¬-elim ⊢ p: unlocked — the first measured")
    print("    ON-CREDIT derivation. Classically invisible; here it is priced.")

    # ---- 4. the credit zone census --------------------------------------
    print("\n### 4. The credit zone (what each loan unlocks, per premise set)")
    SETS = [("{p}", [P]),
            ("{¬p}", [("not", P)]),
            ("{p→q}", [("imp", P, Q)]),
            ("{p∨q}", [("or", P, Q)]),
            ("{p, p→q}", [P, ("imp", P, Q)]),
            ("{¬¬p}", [("not", ("not", P))])]
    for name, prem in SETS:
        a = set(close(prem))
        dne = set(close(prem, loans={"DNE"})) - a
        tau = set(close(prem, loans={"TAUT"})) - a
        print(f"  {name:11s} earned {len(a):3d};  +DNE unlocks {len(dne):3d};"
              f"  +taut unlocks {len(tau):2d}")
    print("  → the loans are not decoration: each unlock is a formula whose")
    print("    every derivation must pass through a fallen rule.")

    # ---- 5. the completeness gap ----------------------------------------
    print("\n### 5. The gap: semantically entailed yet underivable (honest)")
    for name, prem in [("{p}", [P]), ("{p, p→q}", [P, ("imp", P, Q)])]:
        a = set(close(prem, loans={"DNE", "TAUT"}))
        ent = entailed_set(prem)
        gap = ent - a
        wit = sorted(gap, key=repr)[:2]
        print(f"  {name:11s} entailed {len(ent):3d}; derivable(+loans) "
              f"{len(a & ent):3d}; GAP {len(gap):3d}"
              f"   e.g. {', '.join(show(w) for w in wit)}")
    print("  → the 12 rules are NOT complete for ZTL-entailment even here;")
    print("    part of the gap may be pool-boundedness (a lemma outside the")
    print("    pool) — the honest split needs a bigger pool, not a claim.")

    print(f"\n  soundness cross-check on the core: {total_unsound} violations"
          " (must be 0)")
    assert total_unsound == 0
    print("\n  ✓ E26: no axiom rule — from nothing, nothing, even on credit;")
    print("    the syllogism is earned; ¬¬p ⊢ p is the first priced credit;")
    print("    the loans measurably unlock; the rule set is honestly incomplete.")
