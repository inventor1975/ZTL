# -*- coding: utf-8 -*-
"""
ZTL quantifier tableaux (finite domain).

The rules continue the zero-trust signature: weak signs (N={F,Z}) only
in F-polarity, T-polarity demands strict ones:

    T:∀xφ → T:φ(a₁),…,T:φ(aₙ)      F:∀xφ → N:φ(a₁) | … | N:φ(aₙ)
    T:∃xφ → T:φ(a₁) | … | T:φ(aₙ)  F:∃xφ → N:φ(a₁),…,N:φ(aₙ)

Greediness: quantified formulas are classical (P≡T, N≡F on compounds).
Check (MEASURED): tableau decisions against semantic enumeration of all
interpretations (the fo-battery from quantifiers.py + additions),
domains 1–2.
"""

from itertools import product

from ztl import T, F, Z, VALUES, OPS2
from tableau import ST, SF, SP, SN, CLASSIC, TABLEAU_RULES
from quantifiers import ev_fo, interps_for, RULES_FO, VALIDITIES_C, P, Q, x, y


def subst(phi, var, val):
    op = phi[0]
    if op in ("all", "ex"):
        if phi[1] == var:
            return phi                      # variable shadowed
        return (op, phi[1], subst(phi[2], var, val))
    if op == "not":
        return ("not", subst(phi[1], var, val))
    if op in OPS2:
        return (op, subst(phi[1], var, val), subst(phi[2], var, val))
    return (op,) + tuple(val if t == var else t for t in phi[1:])


def closes(nodes, dom):
    """True if the tableau closes. nodes: list of (sign, closed formula)."""
    atom_signs = {}
    first = None
    rest = []
    for sign, phi in nodes:
        op = phi[0]
        if op == "not" or op in OPS2 or op in ("all", "ex"):
            s = sign & CLASSIC              # greediness: a compound is never Z
            if not s:
                return True
            if s == CLASSIC:
                continue                    # uninformative sign
            if first is None:
                first = (s, phi)
            else:
                rest.append((s, phi))
        else:                               # atomic fact P(a…)
            cur = atom_signs.get(phi, frozenset(VALUES)) & sign
            if not cur:
                return True
            atom_signs[phi] = cur
    if first is None:
        return False                        # saturated open branch
    s, phi = first
    base = rest + [(sg, at) for at, sg in sorted(atom_signs.items())]
    op = phi[0]
    if op in ("all", "ex"):
        v, body = phi[1], phi[2]
        insts = [subst(body, v, d) for d in dom]
        strict_all = (op == "all") == (s == ST)   # ∀ under T and ∃ under F — one branch
        lax = SN if s == SF else ST
        if strict_all:
            sg = ST if s == ST else SN
            branches = [[(sg, inst) for inst in insts]]
        else:
            sg = ST if s == ST else SN
            branches = [[(sg, inst)] for inst in insts]
        for br in branches:
            if not closes(base + br, dom):
                return False
        return True
    polarity = T if s == ST else F
    args = phi[1:]
    for branch in TABLEAU_RULES[op][polarity]:
        new_nodes = base + [(sign, args[slot]) for slot, sign in branch]
        if not closes(new_nodes, dom):
            return False
    return True


def prove_fo(premises, conclusion, dom, const=0):
    """Γ ⊢ φ on domain dom; the free variable x reads as element const."""
    g = lambda f: subst(f, x, const)
    nodes = [(ST, g(p)) for p in premises] + [(SN, g(conclusion))]
    return closes(nodes, dom)


def sem_entails(premises, conclusion, dom):
    """Semantic entailment on a fixed domain (enumeration)."""
    for interp in interps_for(premises + [conclusion], dom):
        env = {x: 0}
        if all(ev_fo(p, dom, interp, env) == T for p in premises) \
                and ev_fo(conclusion, dom, interp, env) != T:
            return False
    return True


BATTERY = [(name, prems, concl) for name, prems, concl, _ in RULES_FO] + \
          [(name, [], phi) for name, phi in VALIDITIES_C] + [
    ("distribution ∀∧ forward", [("all", y, ("and", (P, y), (Q, y)))],
     ("and", ("all", y, (P, y)), ("all", y, (Q, y)))),
    ("distribution ∀∧ backward", [("and", ("all", y, (P, y)), ("all", y, (Q, y)))],
     ("all", y, ("and", (P, y), (Q, y)))),
    ("∃ from ∀", [("all", y, (P, y))], ("ex", y, (P, y))),
    ("quant. De Morgan as a rule", [("not", ("all", y, (P, y)))],
     ("ex", y, ("not", (P, y)))),
]


if __name__ == "__main__":
    print("=" * 72)
    print("ZTL QUANTIFIER TABLEAUX: check against semantics on domains 1–2")
    print("=" * 72)
    total, mism = 0, []
    for n in (1, 2):
        dom = list(range(n))
        for name, prems, concl in BATTERY:
            skip = any("R" in str(f) for f in prems + [concl]) and n > 2
            sem = sem_entails(prems, concl, dom)
            syn = prove_fo(prems, concl, dom)
            total += 1
            mark = "✓" if sem == syn else "✗ DIVERGENCE"
            if sem != syn:
                mism.append((n, name, sem, syn))
            if n == 2:
                verdict = "derivable" if syn else "not derivable"
                print(f"  |D|={n}  {mark} {name}: {verdict}")
    print(f"\nPairs checked (tableaux against enumeration): {total}")
    if mism:
        for m in mism:
            print("  ✗", m)
        raise SystemExit("Divergence — stop.")
    print("  ✓ ALL decisions coincided: the quantifier tableaux are sound and complete on the battery")
