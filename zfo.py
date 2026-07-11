# -*- coding: utf-8 -*-
"""
Expedition E17: first order over ARBITRARY domains — parameter tableaux.

Finite-domain quantifiers (E: quantifiers.py, tableau_fo.py) unfold ∀/∃
into finite folds. Over arbitrary domains that is impossible; the
standard cure is parameter (free-variable) tableaux with γ/δ rules —
and the zero-trust sign discipline carries over exactly:

    γ (reusable, all parameters):   T:∀xφ → T:φ(c) for every c
                                    F:∃xφ → N:φ(c) for every c
    δ (fresh parameter, once):      F:∀xφ → N:φ(c*) , c* fresh
                                    T:∃xφ → T:φ(c*) , c* fresh

The δ-rules introduce fresh witnesses exactly where the CALCULUS allows
weak signs (F-polarity) or demands a strict witness (T:∃) — the same
signature as propositionally: proving costs strict certificates,
refuting settles for weak ones.

Status honesty: soundness is MEASURED (proved sequents re-checked by
total enumeration on finite domains; open saturated branches yield
countermodels that are VERIFIED by evaluation). Completeness is the
standard Hintikka-saturation argument for finitely-valued signed
tableaux (Hähnle) — argued, not measured. FO-ZTL is undecidable: the
J-guard translation P ↦ P∧P embeds classical FO validity.
"""

import sys
from itertools import product

from ztl import T, F, Z, VALUES, NOT, OPS2
from tableau import ST, SF, SP, SN, CLASSIC, TABLEAU_RULES
from tableau_fo import subst


class BudgetExceeded(Exception):
    pass


def _is_atom(phi):
    return phi[0] not in OPS2 and phi[0] not in ("not", "all", "ex")


def _copy_gammas(gammas):
    return [{"var": g["var"], "body": g["body"], "sg": g["sg"],
             "done": set(g["done"])} for g in gammas]


def solve(pending, atom_cs, gammas, params, budget):
    """Expand a branch. Returns ("closed", None) or
    ("open", (atom_cs, params)) for a SATURATED open branch."""
    pending = list(pending)
    atom_cs = dict(atom_cs)
    gammas = _copy_gammas(gammas)
    params = list(params)
    while True:
        if budget[0] <= 0:
            raise BudgetExceeded
        if pending:
            budget[0] -= 1
            sign, phi = pending.pop()
            if _is_atom(phi):
                cur = atom_cs.get(phi, frozenset(VALUES)) & sign
                if not cur:
                    return ("closed", None)
                atom_cs[phi] = cur
                continue
            s = sign & CLASSIC          # greediness: compounds are classical
            if not s:
                return ("closed", None)
            if s == CLASSIC:
                continue                # uninformative sign
            op = phi[0]
            if op in ("all", "ex"):
                var, body = phi[1], phi[2]
                if (op == "all" and s == ST) or (op == "ex" and s == SF):
                    # γ: reusable, instantiated over all parameters
                    sg = ST if s == ST else SN
                    gammas.append({"var": var, "body": body, "sg": sg,
                                   "done": set()})
                else:
                    # δ: one fresh parameter
                    c = f"#{len(params)}"
                    params.append(c)
                    sg = ST if s == ST else SN
                    pending.append((sg, subst(body, var, c)))
                continue
            # propositional expansion
            polarity = T if s == ST else F
            args = phi[1:]
            for br in TABLEAU_RULES[op][polarity]:
                new_pending = pending + [(sg, args[slot]) for slot, sg in br]
                st, info = solve(new_pending, atom_cs, gammas, params, budget)
                if st == "open":
                    return ("open", info)
            return ("closed", None)
        # no pending work: fire γ instantiations
        if not params:
            params.append("#0")
        progress = False
        for g in gammas:
            for c in list(params):
                if c not in g["done"]:
                    g["done"].add(c)
                    pending.append((g["sg"], subst(g["body"], g["var"], c)))
                    progress = True
        if not progress:
            return ("open", (atom_cs, params))   # saturated open branch


def initial_params(formulas):
    out = set()

    def walk(phi):
        if _is_atom(phi):
            for t in phi[1:]:
                if isinstance(t, str) and t.startswith("#"):
                    out.add(t)
        elif phi[0] in ("all", "ex"):
            walk(phi[2])
        elif phi[0] == "not":
            walk(phi[1])
        else:
            walk(phi[1]); walk(phi[2])
    for f in formulas:
        walk(f)
    return sorted(out)


def prove(premises, conclusion, budget_units=2000):
    """Γ ⊢ φ over arbitrary domains. Returns ("valid", None),
    ("countermodel", (values, domain)) or ("budget", None)."""
    nodes = [(ST, g) for g in premises] + [(SN, conclusion)]
    params = initial_params(premises + [conclusion])
    sys.setrecursionlimit(100000)
    try:
        st, info = solve(nodes, {}, [], params, [budget_units])
    except BudgetExceeded:
        return ("budget", None)
    if st == "closed":
        return ("valid", None)
    atom_cs, dom = info
    values = {atom: sorted(allowed)[-1] for atom, allowed in atom_cs.items()}
    return ("countermodel", (values, dom))       # sorted: F<T<Z → prefers Z


# ------------------------------------------------- evaluation and checks
def ev_ground(phi, dom, values):
    op = phi[0]
    if op == "all":
        return T if all(ev_ground(subst(phi[2], phi[1], c), dom, values) == T
                        for c in dom) else F
    if op == "ex":
        return T if any(ev_ground(subst(phi[2], phi[1], c), dom, values) == T
                        for c in dom) else F
    if op == "not":
        return NOT(ev_ground(phi[1], dom, values))
    if op in OPS2:
        return OPS2[op](ev_ground(phi[1], dom, values),
                        ev_ground(phi[2], dom, values))
    return values.get(phi, Z)


def _arities(formulas):
    ar = {}

    def walk(phi):
        if _is_atom(phi):
            ar[phi[0]] = len(phi) - 1
        elif phi[0] in ("all", "ex"):
            walk(phi[2])
        elif phi[0] == "not":
            walk(phi[1])
        else:
            walk(phi[1]); walk(phi[2])
    for f in formulas:
        walk(f)
    return ar


def finite_countermodel(premises, conclusion, max_n=2):
    """Total enumeration over domains 1..max_n (parameters read as e0)."""
    forms = premises + [conclusion]
    ar = _arities(forms)
    consts = initial_params(forms)
    for n in range(1, max_n + 1):
        dom = [f"e{i}" for i in range(n)]
        ren = {c: dom[0] for c in consts}
        insts = []
        for pred, k in sorted(ar.items()):
            for combo in product(dom, repeat=k):
                insts.append((pred,) + combo)
        gforms = []
        for f in forms:
            g = f
            for c, e in ren.items():
                g = subst(g, c, e)
            gforms.append(g)
        for combo in product(VALUES, repeat=len(insts)):
            values = dict(zip(insts, combo))
            if all(ev_ground(g, dom, values) == T for g in gforms[:-1]) \
                    and ev_ground(gforms[-1], dom, values) != T:
                return (values, dom)
    return None


# ---------------------------------------------------------------- battery
P_ = lambda t: ("P", t)
Q_ = lambda t: ("Q", t)
R_ = lambda s, t: ("R", s, t)
G_ = lambda t: ("and", ("P", t), ("P", t))       # J_T guard

BATTERY = [
    # (name, premises, conclusion, expected)
    ("UI rule: ∀yP ⊨ P(a)",
     [("all", "y", P_("y"))], P_("#a"), "valid"),
    ("UI law: ⊨ ∀yP → P(a)",
     [], ("imp", ("all", "y", P_("y")), P_("#a")), "valid"),
    ("EG rule: P(a) ⊨ ∃yP",
     [P_("#a")], ("ex", "y", P_("y")), "valid"),
    ("∀-distribution: ∀y(P∧Q) ⊨ ∀yP",
     [("all", "y", ("and", P_("y"), Q_("y")))], ("all", "y", P_("y")),
     "valid"),
    ("∀¬ ⊨ ¬∃",
     [("all", "y", ("not", P_("y")))], ("not", ("ex", "y", P_("y"))),
     "valid"),
    ("quantifier swap: ∃x∀yR ⊨ ∀y∃xR",
     [("ex", "x", ("all", "y", R_("x", "y")))],
     ("all", "y", ("ex", "x", R_("x", "y"))), "valid"),
    ("modus ponens under ∀: ∀x(P→Q), ∀xP ⊨ ∀xQ",
     [("all", "x", ("imp", P_("x"), Q_("x"))), ("all", "x", P_("x"))],
     ("all", "x", Q_("x")), "valid"),
    ("guarded drinker: ⊨ ∃y(G(y) → ∀zG(z)), G = J_T·P",
     [], ("ex", "y", ("imp", G_("y"), ("all", "z", G_("z")))), "valid"),
    ("¬∃ ⊭ ∀¬ (Z hides)",
     [("not", ("ex", "y", P_("y")))], ("all", "y", ("not", P_("y"))),
     "countermodel"),
    ("EG law fails: ⊭ P(a) → ∃yP",
     [], ("imp", P_("#a"), ("ex", "y", P_("y"))), "countermodel"),
    ("unguarded drinker fails: ⊭ ∃y(P(y) → ∀zP(z))",
     [], ("ex", "y", ("imp", P_("y"), ("all", "z", P_("z")))),
     "budget"),                # branch spawns witnesses forever
    ("quantified LEM fails: ⊭ ∀y(P∨¬P)",
     [], ("all", "y", ("or", P_("y"), ("not", P_("y")))), "countermodel"),
    ("swap converse fails: ∀y∃xR ⊭ ∃x∀yR",
     [("all", "y", ("ex", "x", R_("x", "y")))],
     ("ex", "x", ("all", "y", R_("x", "y"))), "budget"),
]


if __name__ == "__main__":
    print("=" * 72)
    print("E17. FIRST ORDER OVER ARBITRARY DOMAINS: PARAMETER TABLEAUX")
    print("=" * 72)
    print("\n  γ (reusable): T:∀, F:∃   δ (fresh): F:∀, T:∃ —")
    print("  fresh witnesses live exactly where the weak signs live.\n")

    bad = 0
    for name, prems, concl, expected in BATTERY:
        verdict, info = prove(prems, concl)
        ok = verdict == expected
        detail = ""
        if verdict == "valid":
            # soundness cross-check: no finite counterexample may exist
            cex = finite_countermodel(prems, concl)
            ok = ok and cex is None
            detail = "finite check 1–2: no counterexample" if cex is None \
                else f"✗ FINITE COUNTEREXAMPLE {cex}"
        elif verdict == "countermodel":
            values, dom = info
            all_prem = all(ev_ground(p2, dom, values) == T for p2 in prems)
            concl_v = ev_ground(concl, dom, values)
            ok = ok and all_prem and concl_v != T
            zs = sum(1 for v in values.values() if v == Z)
            detail = (f"|D|={len(dom)}, conclusion={concl_v}, "
                      f"Z-atoms={zs} — model VERIFIED" if all_prem
                      else "✗ MODEL DOES NOT CHECK OUT")
        elif verdict == "budget":
            # non-terminating branch: certify invalidity finitely
            cex = finite_countermodel(prems, concl)
            ok = ok and cex is not None
            detail = (f"tableau spawns witnesses forever (FO honesty); "
                      f"invalidity certified by a finite countermodel, "
                      f"|D|={len(cex[1])}" if cex
                      else "✗ NO FINITE COUNTEREXAMPLE FOUND")
        mark = "✓" if ok else "✗"
        if not ok:
            bad += 1
        print(f"  {mark} {name}")
        print(f"      verdict: {verdict}; {detail}")

    print(f"\n### Cross-check: {len(BATTERY) - bad} of {len(BATTERY)}"
          f" verdicts confirmed"
          + (" — ALL verdicts cross-checked ✓" if bad == 0 else " ✗"))

    print("\n### Undecidability, honestly")
    print("  The guard G = P∧P (J_T) makes every atom classical: the guarded")
    print("  translation embeds classical FO validity into FO-ZTL — validity")
    print("  is undecidable, the tableaux give semi-decidability (the guarded")
    print("  drinker above needed the classic two γ-rounds). Completeness of")
    print("  the parameter tableaux is the standard Hintikka saturation for")
    print("  finitely-valued signed systems (Hähnle) — argued; soundness and")
    print("  every open verdict are MEASURED above.")
    if bad:
        raise SystemExit("FO BATTERY FAILED — stop.")
