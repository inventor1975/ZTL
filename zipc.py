# -*- coding: utf-8 -*-
"""
E20 — the honest delta against intuitionism (VR Part II, step 1).

ZTL and IPC (intuitionistic propositional calculus) both refuse to hand
out classical truth for free, so the comparison is owed. This stand
MEASURES the delta instead of narrating it.

Instruments:
  * IPC side: a real decision procedure — Dyckhoff's contraction-free
    sequent calculus G4ip (LJT, JSL 1992) — calibrated against the
    canonical statuses from the literature (the `ipc_canon` column
    below); any disagreement turns the stand red.
  * ZTL side: the native `entails` of the keel (designated {T}).
  * CPC side: enumeration over classical assignments.

What is measured:
  1. LAWS: a canonical battery, three columns (CPC / IPC / ZTL);
     both inclusion failures exhibited by explicit witnesses:
     IPC ⊬⊇ ZTL and ZTL ⊬⊇ IPC — the two logics are INCOMPARABLE
     as sets of laws (both sit strictly inside CPC).
  2. RULES: the 14-rule classical battery of the keel, judged as
     Γ ⊢ φ by G4ip versus Γ ⊨ φ by ZTL — verdict-by-verdict.
  3. Disjunction property: IPC has it (Gödel 1932); ZTL loses it —
     witness measured, plus a census over a generated formula pool.
  4. ¬¬-transparency: ⊨_ZTL ¬¬A ⟺ ⊨_ZTL A totally on the pool;
     contrast: Glivenko 1929 (IPC ⊢ ¬¬A for classically valid A)
     verified by the prover on every CPC-valid battery law.

Scope note (honest): the shared language is {¬, ∧, ∨, →} plus ↔ read
as (A→B)∧(B→A) on the IPC side; ZTL's primitive ⊕ has no canonical
intuitionistic reading and is left out.
"""

from itertools import product

from ztl import T, F, Z, ev, atoms, show
from entailment import entails, RULES

BOT = "⊥"


# ---------------------------------------------------------------------------
# Translation ZTL formula -> IPC formula ({atoms, ⊥, and, or, imp})
# ---------------------------------------------------------------------------
def to_ipc(phi):
    if isinstance(phi, str):
        if phi in (T, F, Z):
            raise ValueError(f"constant {phi} has no agreed IPC reading")
        return phi
    op = phi[0]
    if op == "not":
        return ("imp", to_ipc(phi[1]), BOT)
    if op == "xnor":
        a, b = to_ipc(phi[1]), to_ipc(phi[2])
        return ("and", ("imp", a, b), ("imp", b, a))
    if op == "xor":
        raise ValueError("⊕ has no canonical intuitionistic reading — out of scope")
    return (op, to_ipc(phi[1]), to_ipc(phi[2]))


# ---------------------------------------------------------------------------
# G4ip — Dyckhoff's contraction-free calculus for IPC (decision procedure)
# ---------------------------------------------------------------------------
_memo = {}


def prove(gamma, goal):
    """Γ ⊢_IPC goal? gamma: frozenset of formulas."""
    key = (gamma, goal)
    if key in _memo:
        return _memo[key]
    res = _prove(gamma, goal)
    _memo[key] = res
    return res


def _prove(gamma, goal):
    g = set(gamma)
    # --- deterministic (invertible, non-branching) left saturation ---
    changed = True
    while changed:
        changed = False
        if BOT in g or goal in g:
            return True
        for x in list(g):
            if isinstance(x, str):
                continue
            if x[0] == "and":
                g.discard(x); g.add(x[1]); g.add(x[2])
                changed = True
            elif x[0] == "imp":
                a, b = x[1], x[2]
                if isinstance(a, str):
                    if a == BOT:                      # ⊥→B is trivially true
                        g.discard(x); changed = True
                    elif a in g:                      # →L for atoms: a, a→B ⇒ B
                        g.discard(x); g.add(b); changed = True
                elif a[0] == "and":                   # (C∧D)→B ⇒ C→(D→B)
                    g.discard(x); g.add(("imp", a[1], ("imp", a[2], b)))
                    changed = True
                elif a[0] == "or":                    # (C∨D)→B ⇒ C→B, D→B
                    g.discard(x); g.add(("imp", a[1], b)); g.add(("imp", a[2], b))
                    changed = True
    if BOT in g or goal in g:
        return True
    # --- invertible right rules ---
    if not isinstance(goal, str):
        if goal[0] == "and":
            fg = frozenset(g)
            return prove(fg, goal[1]) and prove(fg, goal[2])
        if goal[0] == "imp":
            return prove(frozenset(g | {goal[1]}), goal[2])
    # --- invertible branching left rule: ∨L ---
    for x in g:
        if not isinstance(x, str) and x[0] == "or":
            rest = g - {x}
            return (prove(frozenset(rest | {x[1]}), goal)
                    and prove(frozenset(rest | {x[2]}), goal))
    # --- non-invertible choices ---
    fg = frozenset(g)
    if not isinstance(goal, str) and goal[0] == "or":
        if prove(fg, goal[1]) or prove(fg, goal[2]):
            return True
    for x in g:
        if not isinstance(x, str) and x[0] == "imp" \
                and not isinstance(x[1], str) and x[1][0] == "imp":
            c, d, b = x[1][1], x[1][2], x[2]
            rest = g - {x}
            if prove(frozenset(rest | {("imp", d, b)}), ("imp", c, d)) \
                    and prove(frozenset(rest | {b}), goal):
                return True
    return False


def ipc_valid(phi):
    return prove(frozenset(), to_ipc(phi))


def ipc_derives(premises, conclusion):
    return prove(frozenset(to_ipc(p) for p in premises), to_ipc(conclusion))


# ---------------------------------------------------------------------------
# CPC and ZTL judges
# ---------------------------------------------------------------------------
def cpc_valid(phi):
    names = sorted(atoms(phi, set()))
    return all(ev(phi, dict(zip(names, combo))) == T
               for combo in product((T, F), repeat=len(names)))


def ztl_valid(phi):
    return entails([], phi) is None


# ---------------------------------------------------------------------------
# The battery of laws. ipc_canon = the status IPC is REQUIRED to report
# (textbook: Troelstra–van Dalen; Gödel 1932 for WLEM/Dummett; the stand
# goes red if the prover disagrees — this is the instrument's calibration).
# ---------------------------------------------------------------------------
p, q, r = "p", "q", "r"
n = lambda a: ("not", a)

LAWS = [
    # name, formula, ipc_canon
    ("identity            p→p",                 ("imp", p, p),                                        True),
    ("LEM                 p∨¬p",                ("or", p, n(p)),                                      False),
    ("weak LEM            ¬p∨¬¬p",              ("or", n(p), n(n(p))),                                False),
    ("DNE                 ¬¬p→p",               ("imp", n(n(p)), p),                                  False),
    ("DNI                 p→¬¬p",               ("imp", p, n(n(p))),                                  True),
    ("triple-neg          ¬¬¬p→¬p",             ("imp", n(n(n(p))), n(p)),                            True),
    ("triple-neg-conv     ¬p→¬¬¬p",             ("imp", n(p), n(n(n(p)))),                            True),
    ("EFQ                 (p∧¬p)→q",            ("imp", ("and", p, n(p)), q),                         True),
    ("EFQ-neg             ¬p→(p→q)",            ("imp", n(p), ("imp", p, q)),                         True),
    ("non-contradiction   ¬(p∧¬p)",             n(("and", p, n(p))),                                  True),
    ("K                   q→(p→q)",             ("imp", q, ("imp", p, q)),                            True),
    ("S                   (p→(q→r))→((p→q)→(p→r))",
     ("imp", ("imp", p, ("imp", q, r)), ("imp", ("imp", p, q), ("imp", p, r))),                       True),
    ("Peirce              ((p→q)→p)→p",         ("imp", ("imp", ("imp", p, q), p), p),                False),
    ("contraposition      (p→q)→(¬q→¬p)",       ("imp", ("imp", p, q), ("imp", n(q), n(p))),          True),
    ("contraposition-conv (¬q→¬p)→(p→q)",       ("imp", ("imp", n(q), n(p)), ("imp", p, q)),          False),
    ("DM ¬∧→∨¬            ¬(p∧q)→(¬p∨¬q)",      ("imp", n(("and", p, q)), ("or", n(p), n(q))),        False),
    ("DM ∨¬→¬∧            (¬p∨¬q)→¬(p∧q)",      ("imp", ("or", n(p), n(q)), n(("and", p, q))),        True),
    ("DM ¬∨→∧¬            ¬(p∨q)→(¬p∧¬q)",      ("imp", n(("or", p, q)), ("and", n(p), n(q))),        True),
    ("DM ∧¬→¬∨            (¬p∧¬q)→¬(p∨q)",      ("imp", ("and", n(p), n(q)), n(("or", p, q))),        True),
    ("¬¬LEM               ¬¬(p∨¬p)",            n(n(("or", p, n(p)))),                                True),
    ("Dummett             (p→q)∨(q→p)",         ("or", ("imp", p, q), ("imp", q, p)),                 False),
    ("distribution        p∧(q∨r)→(p∧q)∨(p∧r)",
     ("imp", ("and", p, ("or", q, r)), ("or", ("and", p, q), ("and", p, r))),                         True),
    ("curry               ((p∧q)→r)→(p→(q→r))",
     ("imp", ("imp", ("and", p, q), r), ("imp", p, ("imp", q, r))),                                   True),
    ("uncurry             (p→(q→r))→((p∧q)→r)",
     ("imp", ("imp", p, ("imp", q, r)), ("imp", ("and", p, q), r)),                                   True),
    ("idempotence-intro   p→p∧p",               ("imp", p, ("and", p, p)),                            True),
    ("idempotence-elim    p∧p→p",               ("imp", ("and", p, p), p),                            True),
    ("∧-comm              p∧q→q∧p",             ("imp", ("and", p, q), ("and", q, p)),                True),
]


def run_laws():
    print("-- 1. LAWS: CPC / IPC / ZTL, three verdicts per formula --")
    rows = []
    calib_bad = []
    for name, phi, canon in LAWS:
        c, i, z = cpc_valid(phi), ipc_valid(phi), ztl_valid(phi)
        rows.append((name, phi, c, i, z))
        if i != canon:
            calib_bad.append(name)
        mark = lambda b: "✓" if b else "✗"
        print(f"  CPC {mark(c)}  IPC {mark(i)}  ZTL {mark(z)}   {name}")
    if calib_bad:
        print(f"  PROVER CALIBRATION FAILED on: {calib_bad}")
        raise SystemExit(1)
    print(f"  Prover calibration: all {len(LAWS)} IPC verdicts match the canon ✓")

    ipc_not_ztl = [(nm, phi) for nm, phi, c, i, z in rows if i and not z]
    ztl_not_ipc = [(nm, phi) for nm, phi, c, i, z in rows if z and not i]
    non_cpc = [(nm) for nm, phi, c, i, z in rows if (i or z) and not c]
    print(f"\n  IPC-valid but ZTL-invalid: {len(ipc_not_ztl)}")
    for nm, phi in ipc_not_ztl:
        cex = entails([], phi)
        print(f"    {show(phi)}   [ZTL counterexample: "
              + ", ".join(f"{k}={v}" for k, v in sorted(cex.items())) + "]")
    print(f"  ZTL-valid but IPC-invalid: {len(ztl_not_ipc)}")
    for nm, phi in ztl_not_ipc:
        print(f"    {show(phi)}   [IPC: no proof — G4ip search fails]")
    assert ipc_not_ztl and ztl_not_ipc
    assert not non_cpc, "a law escaped CPC — impossible"
    print("  Both witness lists are non-empty and every law sits inside CPC:")
    print("  ZTL and IPC are INCOMPARABLE sublogics of classical logic.")
    return rows


def run_rules():
    print("\n-- 2. RULES: the 14-rule classical battery, Γ⊢ (IPC) vs Γ⊨ (ZTL) --")
    agree = 0
    for name, prems, concl in RULES:
        i = ipc_derives(prems, concl)
        z = entails(prems, concl) is None
        mark = lambda b: "✓" if b else "✗"
        tag = "SAME" if i == z else "DIFF"
        agree += (i == z)
        print(f"  IPC {mark(i)}  ZTL {mark(z)}  [{tag}]  {name}")
    print(f"  Rule verdicts coincide: {agree} of {len(RULES)}.")
    return agree


# ---------------------------------------------------------------------------
# Formula pool for the census checks
# ---------------------------------------------------------------------------
def build_pool(atoms_=("p", "q"), depth=2):
    layers = [list(atoms_)]
    for _ in range(depth):
        prev = [f for layer in layers for f in layer]
        new = [("not", a) for a in layers[-1]]
        for op in ("and", "or", "imp"):
            new += [(op, a, b) for a in layers[-1] for b in prev]
            new += [(op, a, b) for a in prev for b in layers[-1]
                    if (op, a, b) not in new]
        layers.append(new)
    return [f for layer in layers for f in layer]


def run_dp(pool):
    print("\n-- 3. DISJUNCTION PROPERTY --")
    w = ("or", n(p), n(n(p)))
    ok = ztl_valid(w) and not ztl_valid(n(p)) and not ztl_valid(n(n(p)))
    assert ok
    print(f"  IPC has DP (Gödel 1932): ⊢A∨B forces ⊢A or ⊢B.")
    print(f"  ZTL witness: ⊨ {show(w)}, yet ⊭ {show(n(p))} and ⊭ {show(n(n(p)))}")
    print("  → ZTL LOSES the disjunction property: ∨ earns T when every")
    print("    classical reading forces it, not when a disjunct is certified.")
    sub = build_pool(atoms_=("p",), depth=2)
    census = [("or", a, b) for a in sub for b in sub
              if ztl_valid(("or", a, b))
              and not ztl_valid(a) and not ztl_valid(b)]
    print(f"  Census: all ∨-pairs over the one-atom depth-2 pool "
          f"({len(sub)}² pairs): {len(census)} ZTL-valid disjunctions with "
          f"both disjuncts invalid\n  (e.g. {show(census[0])}).")


def run_dneg(pool, rows):
    print("\n-- 4. ¬¬-TRANSPARENCY vs GLIVENKO --")
    bad = [f for f in pool if ztl_valid(f) != ztl_valid(n(n(f)))]
    print(f"  ZTL: ⊨A ⟺ ⊨¬¬A checked on {len(pool)} pool formulas, "
          f"mismatches: {len(bad)} (must be 0)")
    assert not bad
    gliv = [(nm, phi) for nm, phi, c, i, z in rows if c]
    failed = [nm for nm, phi in gliv if not ipc_valid(n(n(phi)))]
    print(f"  IPC (Glivenko 1929): ⊢¬¬A for every CPC-valid battery law — "
          f"{len(gliv) - len(failed)} of {len(gliv)} proved by G4ip "
          f"(failures: {len(failed)}, must be 0)")
    assert not failed
    print("  → In ZTL double negation is verdict-transparent (¬¬ changes no")
    print("    verdict); in IPC ¬¬ is the classical shadow (strictly weaker).")


def main():
    print("=" * 72)
    print("E20: THE DELTA AGAINST INTUITIONISM (G4ip vs the ZTL keel)")
    print("=" * 72)
    rows = run_laws()
    agree = run_rules()
    pool = build_pool()
    print(f"\n  [pool: {len(pool)} formulas over p,q up to depth 2]")
    run_dp(pool)
    run_dneg(pool, rows)
    print("\n" + "=" * 72)
    print("VERDICT: at the level of LAWS ZTL and IPC are INCOMPARABLE")
    print("(each holds laws the other refuses); at the level of RULES the")
    print(f"two agree on {agree} of {len(RULES)} classical inferences.")
    print("ZTL is tabular (3 cells), IPC has no finite matrix (Gödel 1932);")
    print("ZTL loses DP, IPC keeps it; ZTL's ¬¬ is transparent, IPC's is not.")
    print("Same slogan — no truth on credit; different creditors.")
    print("=" * 72)


if __name__ == "__main__":
    main()
