# -*- coding: utf-8 -*-
"""
ZTL quantifiers on finite domains.

By the generating principle:
    ∀x φ = a big conjunction: T if EVERY instance is strictly T, else F
           (one Z-witness poisons the universal — it is not earned);
    ∃x φ = a big disjunction: T if AT LEAST ONE instance is strictly T,
           else F (a Z-candidate does not count as a witness).
Greediness extends: compound formulas (including quantified ones) never
take Z; Z lives only on atomic facts P(a).

Measurements (MEASURED): quantifier laws and rules over all
interpretations of unary P,Q (domains 1..3) and binary R (domains 1..2).
"""

from itertools import product

from ztl import T, F, Z, VALUES, NOT, OPS2


def ev_fo(phi, dom, interp, env):
    """Value of a first-order formula.
    interp: predicate name -> tuple of values (unary: by element;
    binary: interp[name][i][j]). env: variable -> element index."""
    op = phi[0]
    if op == "all":
        vals = [ev_fo(phi[2], dom, interp, {**env, phi[1]: d}) for d in dom]
        return T if all(v == T for v in vals) else F
    if op == "ex":
        vals = [ev_fo(phi[2], dom, interp, {**env, phi[1]: d}) for d in dom]
        return T if any(v == T for v in vals) else F
    if op == "not":
        return NOT(ev_fo(phi[1], dom, interp, env))
    if op in OPS2:
        return OPS2[op](ev_fo(phi[1], dom, interp, env),
                        ev_fo(phi[2], dom, interp, env))
    # atomic fact: ('P', 'x') or ('R', 'x', 'y')
    if len(phi) == 2:
        return interp[op][env[phi[1]]]
    return interp[op][env[phi[1]]][env[phi[2]]]


def unary_interps(dom, names):
    """All interpretations of the unary predicates names on the domain."""
    per_pred = list(product(VALUES, repeat=len(dom)))
    for combo in product(per_pred, repeat=len(names)):
        yield dict(zip(names, combo))


def binary_interps(dom, name):
    """All interpretations of one binary predicate."""
    n = len(dom)
    for flat in product(VALUES, repeat=n * n):
        yield {name: tuple(tuple(flat[i * n + j] for j in range(n))
                           for i in range(n))}


def preds_of(phi, acc=None):
    if acc is None:
        acc = {}
    op = phi[0]
    if op in ("all", "ex"):
        preds_of(phi[2], acc)
    elif op == "not":
        preds_of(phi[1], acc)
    elif op in OPS2:
        preds_of(phi[1], acc)
        preds_of(phi[2], acc)
    else:
        acc[op] = len(phi) - 1
    return acc


def interps_for(formulas, dom):
    """All joint interpretations of all predicates of a formula set."""
    arity = {}
    for f in formulas:
        arity.update(preds_of(f))
    unary = sorted(n for n, a in arity.items() if a == 1)
    binary = sorted(n for n, a in arity.items() if a == 2)
    assert len(binary) <= 1, "one binary predicate supported"
    if binary:
        for bi in binary_interps(dom, binary[0]):
            if unary:
                for ui in unary_interps(dom, unary):
                    yield {**bi, **ui}
            else:
                yield bi
    else:
        yield from unary_interps(dom, unary)


def fo_equal(lhs, rhs, max_dom=3):
    """First counterexample to the identity, else None."""
    for n in range(1, max_dom + 1):
        dom = list(range(n))
        for interp in interps_for([lhs, rhs], dom):
            a, b = ev_fo(lhs, dom, interp, {}), ev_fo(rhs, dom, interp, {})
            if a != b:
                return (dom, interp, a, b)
    return None


def fo_valid(phi, max_dom=3):
    for n in range(1, max_dom + 1):
        dom = list(range(n))
        for interp in interps_for([phi], dom):
            if ev_fo(phi, dom, interp, {}) != T:
                return (dom, interp)
    return None


def fo_entails(premises, conclusion, max_dom=3):
    for n in range(1, max_dom + 1):
        dom = list(range(n))
        for interp in interps_for(premises + [conclusion], dom):
            if all(ev_fo(p, dom, interp, {}) == T for p in premises) \
                    and ev_fo(conclusion, dom, interp, {}) != T:
                return (dom, interp)
    return None


# --- battery: P(a) coded as atom (P, x) with env {x: 0} — "a" = element 0 ---
P, Q = "P", "Q"
x, y = "x", "y"


def fo_entails_const(premises, conclusion, max_dom=3):
    """Like fo_entails, but the free variable x reads as the constant 0."""
    for n in range(1, max_dom + 1):
        dom = list(range(n))
        for interp in interps_for(premises + [conclusion], dom):
            env = {x: 0}
            if all(ev_fo(p, dom, interp, env) == T for p in premises) \
                    and ev_fo(conclusion, dom, interp, env) != T:
                return (dom, interp)
    return None


def fo_valid_const(phi, max_dom=3):
    for n in range(1, max_dom + 1):
        dom = list(range(n))
        for interp in interps_for([phi], dom):
            if ev_fo(phi, dom, interp, {x: 0}) != T:
                return (dom, interp)
    return None


IDENTITIES = [
    ("De Morgan ∀:  ¬∀xP = ∃x¬P",
     ("not", ("all", x, (P, x))), ("ex", x, ("not", (P, x)))),
    ("De Morgan ∃:  ¬∃xP = ∀x¬P",
     ("not", ("ex", x, (P, x))), ("all", x, ("not", (P, x)))),
    ("distribution of ∀ over ∧: ∀x(P∧Q) = ∀xP ∧ ∀xQ",
     ("all", x, ("and", (P, x), (Q, x))),
     ("and", ("all", x, (P, x)), ("all", x, (Q, x)))),
    ("distribution of ∃ over ∨: ∃x(P∨Q) = ∃xP ∨ ∃xQ",
     ("ex", x, ("or", (P, x), (Q, x))),
     ("or", ("ex", x, (P, x)), ("ex", x, (Q, x)))),
]

VALIDITIES_C = [
    ("UI law: ∀yP(y) → P(a)",
     ("imp", ("all", y, (P, y)), (P, x))),
    ("EG law: P(a) → ∃yP(y)",
     ("imp", (P, x), ("ex", y, (P, y)))),
    ("non-emptiness: ∀yP(y) → ∃yP(y)",
     ("imp", ("all", y, (P, y)), ("ex", y, (P, y)))),
    ("quant. LEM: ∀y(P(y)∨¬P(y))",
     ("all", y, ("or", (P, y), ("not", (P, y))))),
    ("the drinker: ∃y(P(y)→∀zP(z))",
     ("ex", y, ("imp", (P, y), ("all", "z", (P, "z"))))),
]

RULES_FO = [
    ("UI rule: ∀yP ⊨ P(a)",
     [("all", y, (P, y))], (P, x), fo_entails_const),
    ("EG rule: P(a) ⊨ ∃yP",
     [(P, x)], ("ex", y, (P, y)), fo_entails_const),
    ("∀¬ ⊨ ¬∃:  ∀y¬P ⊨ ¬∃yP",
     [("all", y, ("not", (P, y)))], ("not", ("ex", y, (P, y))), fo_entails),
    ("¬∃ ⊨ ∀¬:  ¬∃yP ⊨ ∀y¬P",
     [("not", ("ex", y, (P, y)))], ("all", y, ("not", (P, y))), fo_entails),
    ("quantifier swap: ∃x∀yR(x,y) ⊨ ∀y∃xR(x,y)",
     [("ex", x, ("all", y, ("R", x, y)))],
     ("all", y, ("ex", x, ("R", x, y))),
     lambda p, c, max_dom=2: fo_entails(p, c, max_dom)),
]


def fmt_interp(dom, interp):
    parts = []
    for name, val in sorted(interp.items()):
        parts.append(f"{name}={val}")
    return f"|D|={len(dom)}: " + "; ".join(parts)


if __name__ == "__main__":
    print("=" * 72)
    print("ZTL QUANTIFIERS: ∀ = all strictly T; ∃ = a strict T-witness exists")
    print("=" * 72)

    print("\n-- IDENTITIES --")
    for name, lhs, rhs in IDENTITIES:
        cex = fo_equal(lhs, rhs)
        if cex is None:
            print(f"  ✓ {name}")
        else:
            dom, interp, a, b = cex
            print(f"  ✗ {name}   [{fmt_interp(dom, interp)} → {a} vs {b}]")

    print("\n-- LAWS (validity; a = element 0) --")
    for name, phi in VALIDITIES_C:
        cex = fo_valid_const(phi)
        if cex is None:
            print(f"  ✓ {name}")
        else:
            dom, interp = cex
            print(f"  ✗ {name}   [{fmt_interp(dom, interp)}]")

    print("\n-- RULES (entailments) --")
    for name, prems, concl, checker in RULES_FO:
        cex = checker(prems, concl)
        if cex is None:
            print(f"  ✓ {name}")
        else:
            dom, interp = cex
            print(f"  ✗ {name}   [{fmt_interp(dom, interp)}]")
