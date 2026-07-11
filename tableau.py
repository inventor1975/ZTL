# -*- coding: utf-8 -*-
"""
Signed tableaux for ZTL (the Rousseau/Hähnle architecture for
finitely-valued logics).

Signs are sets of values:
    T = {T}        strict truth
    F = {F}        strict falsehood
    P = {T, Z}     "possibly T" (non-falsehood)
    N = {F, Z}     "did not earn T" (non-truth)

The rules are derived from the preimages of the ZTL tables and CARRY the
zero-trust signature: T-polarity demands strict certificates (signs T/F
only), F-polarity settles for weak ones (P/N). Classical tableaux are
the same rules with P≡T and N≡F; the unglueing is Z's entire
contribution.

The greediness theorem degenerates the signs on compound formulas: P≡T,
N≡F (a compound is never Z); Z survives only on atoms — an open branch
with the sign pair P and N on an atom yields a Z-countermodel.

Checks (MEASURED):
  * rule_coverage_check — every rule covers the preimage of its table
    exactly;
  * cross_check — tableau decisions coincide with ⊨ (by enumeration) on
    the entailment.py battery and on all pairs from the generated
    formula pool.
"""

from itertools import product

from ztl import T, F, Z, VALUES, OPS2, ev, atoms, all_envs
from entailment import entails, RULES as RULE_BATTERY

ST = frozenset({T})
SF = frozenset({F})
SP = frozenset({T, Z})   # P: "possibly T"
SN = frozenset({F, Z})   # N: "did not earn T"
CLASSIC = frozenset({T, F})

# Rules: op -> polarity ('T'/'F') -> list of branches;
# a branch = list of pairs (argument slot, sign).
TABLEAU_RULES = {
    "not": {
        T: [[(0, SF)]],
        F: [[(0, SP)]],
    },
    "and": {
        T: [[(0, ST), (1, ST)]],
        F: [[(0, SN)], [(1, SN)]],
    },
    "or": {
        T: [[(0, ST)], [(1, ST)]],
        F: [[(0, SN), (1, SN)]],
    },
    "imp": {
        T: [[(0, SF)], [(1, ST)]],
        F: [[(0, SP), (1, SN)]],
    },
    "xor": {
        T: [[(0, ST), (1, SF)], [(0, SF), (1, ST)]],
        F: [[(0, SP), (1, SP)], [(0, SN), (1, SN)]],
    },
    "xnor": {
        T: [[(0, ST), (1, ST)], [(0, SF), (1, SF)]],
        F: [[(0, SP), (1, SN)], [(0, SN), (1, SP)]],
    },
}


def rule_coverage_check():
    """Every rule must cover the preimage of its table EXACTLY: the
    branches ∪-cover all value combinations with the target output and
    touch none with a different output."""
    problems = []
    for op, per_sign in TABLEAU_RULES.items():
        arity = 1 if op == "not" else 2
        for target, branches in per_sign.items():
            for combo in product(VALUES, repeat=arity):
                if op == "not":
                    from ztl import NOT
                    out = NOT(combo[0])
                else:
                    out = OPS2[op](*combo)
                covered = any(all(combo[slot] in sign for slot, sign in br)
                              for br in branches)
                if (out == target) != covered:
                    problems.append((op, target, combo, out, covered))
    return problems


def _is_atom(phi):
    return isinstance(phi, str) and phi not in VALUES


def tableau_closes(nodes):
    """True if the tableau closes (no model for the signed formula set).
    nodes: list of pairs (sign, formula)."""
    atom_signs = {}
    first_compound = None
    rest = []
    for sign, phi in nodes:
        if _is_atom(phi):
            cur = atom_signs.get(phi, frozenset(VALUES)) & sign
            if not cur:
                return True
            atom_signs[phi] = cur
        elif isinstance(phi, str):           # constant T/F/Z
            if phi not in sign:
                return True
        else:
            s = sign & CLASSIC               # greediness: a compound is never Z
            if not s:
                return True
            if s == CLASSIC:                 # uninformative sign — drop
                continue
            if first_compound is None:
                first_compound = (s, phi)
            else:
                rest.append((s, phi))
    if first_compound is None:
        return False                          # saturated open branch
    s, phi = first_compound
    polarity = T if s == ST else F
    args = phi[1:]
    base = rest + [(sg, at) for at, sg in sorted(atom_signs.items())]
    for branch in TABLEAU_RULES[phi[0]][polarity]:
        new_nodes = base + [(sign, args[slot]) for slot, sign in branch]
        if not tableau_closes(new_nodes):
            return False
    return True


def prove(premises, conclusion):
    """Γ ⊢ φ by tableau: start with T:Γ and N:φ; True = derivable (all
    branches closed)."""
    nodes = [(ST, g) for g in premises] + [(SN, conclusion)]
    return tableau_closes(nodes)


def _pool():
    """Formula pool for the cross-check: depth ≤ 2 over p, q."""
    a = ["p", "q", ("not", "p"), ("not", "q")]
    pool = list(a)
    for op in ("and", "or", "imp", "xor", "xnor"):
        for x in a[:2]:
            for y in a:
                pool.append((op, x, y))
    return pool


def cross_check():
    """Agreement of the tableaux with ⊨ (enumeration): the rule battery
    + the pool of pairs."""
    mismatches = []
    for name, prems, concl in RULE_BATTERY:
        sem = entails(prems, concl) is None
        syn = prove(prems, concl)
        if sem != syn:
            mismatches.append(("battery: " + name, sem, syn))
    pool = _pool()
    n = 0
    for A in pool:
        for B in pool:
            sem = entails([A], B) is None
            syn = prove([A], B)
            n += 1
            if sem != syn:
                mismatches.append((f"{A} |- {B}", sem, syn))
    for A in pool[:8]:
        for B in pool[:8]:
            for C in pool[:8]:
                sem = entails([A, B], C) is None
                syn = prove([A, B], C)
                n += 1
                if sem != syn:
                    mismatches.append((f"{A},{B} |- {C}", sem, syn))
    return n + len(RULE_BATTERY), mismatches


if __name__ == "__main__":
    print("=" * 72)
    print("ZTL SIGNED TABLEAUX: T, F, P={T,Z}, N={F,Z}")
    print("=" * 72)

    probs = rule_coverage_check()
    print("\n-- RULE COVERAGE OF TABLE PREIMAGES --")
    if not probs:
        print("  ✓ all 12 rules coincide exactly with the table preimages")
    else:
        for pr in probs:
            print("  ✗", pr)
        raise SystemExit("Rules do not match the tables — stop.")

    total, mism = cross_check()
    print("\n-- CROSS-CHECK OF TABLEAUX AGAINST ⊨ --")
    print(f"  entailments checked: {total}")
    if not mism:
        print("  ✓ ALL decisions coincided: the calculus is sound and complete on the battery")
    else:
        for m in mism[:10]:
            print("  ✗", m)
        raise SystemExit("Tableau/semantics divergence — stop.")
