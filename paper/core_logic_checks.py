#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
core_logic_checks — every number quoted in paper/ZTL-core-logic.tex, regenerated
from ztl.py (the code is the arbiter) and from the neighbour matrices of
pssl/family.py. Nothing here is typed in by hand; a claim in the paper that this
script does not reproduce is a claim the paper must not make.

Sections, in the order the paper uses them:
  1. the ten tables have no Z cell; the six operators output only T/F
  2. the negative routes to the second five tables fail (3/3/3/5 cells),
     the positive definitions hold (0 cells)
  3. the Suszko discriminator on the depth-2 regression pool (90 compounds):
     ZTL 0/90, K3/LP/weak Kleene 90/90, Ł3 80/90
  4. the delta against Bochvar's external layer: 7 cells, listed
  5. the seven cells change the theorems: on the depth<=2 pool (2926 formulas)
     ZTL's validities are a proper subset of external Bochvar's (212 < 548),
     p→p, p↔p, q→(p→q) in the difference
  6. Tomova's criteria: (1) yes (2) yes (3) broken in exactly one cell (Z,Z)
  7. the price list: 12 laws alive, 14 fallen; 12 rules alive, 2 fallen

Run:  python3 paper/core_logic_checks.py      (from the repository root)
Exit 0 = every number in the paper is reproduced.
"""
import itertools
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
sys.path.insert(0, _ROOT)
sys.path.insert(0, os.path.join(_ROOT, "pssl"))

import ztl                                                    # noqa: E402
import family as Fm                                           # noqa: E402

T, F, Z = ztl.T, ztl.F, ztl.Z
V = [T, F, Z]
N, A, O, I, X, E = ztl.NOT, ztl.AND, ztl.OR, ztl.IMP, ztl.XOR, ztl.XNOR
OPS = {"not": N, "and": A, "or": O, "imp": I, "xor": X, "xnor": E}
SYM = {"and": "∧", "or": "∨", "imp": "→", "xor": "⊕", "xnor": "↔"}
failures = []


def check(cond, msg):
    print(("  ✓ " if cond else "  ✗ ") + msg)
    if not cond:
        failures.append(msg)


def ev(ops, phi, env):
    if isinstance(phi, str):
        return env[phi]
    if phi[0] == "not":
        return ops["not"](ev(ops, phi[1], env))
    return ops[phi[0]](ev(ops, phi[1], env), ev(ops, phi[2], env))


def show(phi):
    if isinstance(phi, str):
        return phi
    if phi[0] == "not":
        return "¬" + show(phi[1])
    return "(" + show(phi[1]) + SYM[phi[0]] + show(phi[2]) + ")"


ENVS = [dict(zip("pq", c)) for c in itertools.product(V, repeat=2)]


def valid(ops, phi):
    return all(ev(ops, phi, e) == T for e in ENVS)


# --- 1. no Z above the atoms -------------------------------------------------
print("1. the ten tables: outputs")
outs = {N(a) for a in V} | {op(a, b) for a in V for b in V for op in (A, O, I, X, E)}
negated = {N(op(a, b)) for a in V for b in V for op in (A, O, I, X)}
check(outs == {T, F} and negated == {T, F}, f"all ten tables output only T/F: {sorted(outs | negated)}")

# --- 2. routes to the second five --------------------------------------------
print("2. classical routes to the negated tables (divergent cells)")
routes = {
    "¬(a∧b) vs ¬a∨¬b": (lambda a, b: N(A(a, b)), lambda a, b: O(N(a), N(b)), 3),
    "¬(a∨b) vs ¬a∧¬b": (lambda a, b: N(O(a, b)), lambda a, b: A(N(a), N(b)), 3),
    "¬(a→b) vs a∧¬b": (lambda a, b: N(I(a, b)), lambda a, b: A(a, N(b)), 3),
    "a↔b vs ¬(a⊕b)": (lambda a, b: E(a, b), lambda a, b: N(X(a, b)), 5),
    "a→b vs ¬a∨b": (lambda a, b: I(a, b), lambda a, b: O(N(a), b), 0),
    "a⊕b vs (a∧¬b)∨(¬a∧b)": (lambda a, b: X(a, b), lambda a, b: O(A(a, N(b)), A(N(a), b)), 0),
    "a↔b vs (a∧b)∨(¬a∧¬b)": (lambda a, b: E(a, b), lambda a, b: O(A(a, b), A(N(a), N(b))), 0),
}
for name, (f, g, expect) in routes.items():
    d = [(a, b) for a in V for b in V if f(a, b) != g(a, b)]
    check(len(d) == expect, f"{name}: {len(d)} cells {d}")

# --- 3. Suszko discriminator on the regression pool ---------------------------
print("3. compounds that take the middle value on the depth-2 pool (audit.py's)")
leaves = ["p", "q", ("not", "p")]
pool90 = [(o, a, b) for o in ("and", "or", "imp", "xor", "xnor") for a in leaves for b in leaves]
pool90 += [("not", f) for f in pool90[:]]
check(len(pool90) == 90, f"pool size {len(pool90)}")
zbad = sum(1 for phi in pool90 if any(ev(OPS, phi, e) == Z for e in ENVS))
check(zbad == 0, f"ZTL: {zbad} of {len(pool90)}")


def mat_ops(m):
    return {"not": m.neg, "and": m.conj, "or": m.disj, "imp": m.imp,
            "xor": lambda a, b: m.disj(m.conj(a, m.neg(b)), m.conj(m.neg(a), b)),
            "xnor": lambda a, b: m.disj(m.conj(a, b), m.conj(m.neg(a), m.neg(b)))}


menvs = [dict(zip("pq", c)) for c in itertools.product(Fm.VALS, repeat=2)]
expect3 = {"K3": 90, "LP": 90, "weak Kleene": 90, "Lukasiewicz L3": 80}
for m in Fm.FAMILY:
    ops = mat_ops(m)
    bad = sum(1 for phi in pool90 if any(ev(ops, phi, e) == Fm.UU for e in menvs))
    check(bad == expect3[m.name], f"{m.name}: {bad} of {len(pool90)}")

# --- 4. Bochvar external layer ------------------------------------------------
print("4. cells where ZTL parts from Bochvar's external layer")
box = {T: 1, F: 0, Z: 0}
tv = lambda b: T if b else F                                   # noqa: E731
BOCH = {"not": lambda a: tv(a == F),
        "and": lambda a, b: tv(box[a] and box[b]),
        "or": lambda a, b: tv(box[a] or box[b]),
        "imp": lambda a, b: tv((not box[a]) or box[b]),
        "xnor": lambda a, b: tv(box[a] == box[b]),
        "xor": lambda a, b: tv(box[a] != box[b])}
total = 0
for k in ("not", "and", "or", "imp", "xnor", "xor"):
    if k == "not":
        d = [(a,) for a in V if BOCH[k](a) != OPS[k](a)]
    else:
        d = [(a, b) for a in V for b in V if BOCH[k](a, b) != OPS[k](a, b)]
    total += len(d)
    print(f"     {SYM.get(k, '¬')}: {len(d)} {d}")
check(total == 7, f"total divergent cells: {total}")

# --- 5. the seven cells change the theorems -----------------------------------
print("5. validities on the depth<=2 pool, ZTL vs external Bochvar")
d1 = ["p", "q"] + [("not", x) for x in ("p", "q")] + \
     [(o, a, b) for o in ("and", "or", "imp", "xor", "xnor") for a in ("p", "q") for b in ("p", "q")]
d2 = [(o, a, b) for o in ("and", "or", "imp", "xor", "xnor") for a in d1 for b in d1] + \
     [("not", x) for x in d1 if not isinstance(x, str)]
pool = d1 + d2
zt = {show(f) for f in pool if valid(OPS, f)}
bt = {show(f) for f in pool if valid(BOCH, f)}
check(len(pool) == 2926, f"pool size {len(pool)}")
check(len(zt) == 212 and len(bt) == 548, f"ZTL {len(zt)} validities, Bochvar {len(bt)}")
check(zt < bt, "ZTL validities are a PROPER subset of external Bochvar's")
diff = sorted(bt - zt, key=len)
print("     first of the difference:", diff[:6])
check({"(p→p)", "(p↔p)", "(q→(p→q))"} <= (bt - zt), "p→p, p↔p, q→(p→q) hold for Bochvar, not for ZTL")

# --- 6. Tomova ----------------------------------------------------------------
print("6. Tomova's natural-implication criteria")
c1 = all(I(a, b) == BOCH["imp"](a, b) for a in (T, F) for b in (T, F))
c2 = all(not (a == T and I(a, b) == T and b != T) for a in V for b in V)
order = {F: 0, Z: 1, T: 2}
broken = [(a, b) for a in V for b in V if order[a] <= order[b] and I(a, b) != T]
check(c1, "(1) classical on {T,F}")
check(c2, "(2) modus ponens preserves the designated value")
check(broken == [(Z, Z)], f"(3) p≤q ⇒ p→q designated, broken exactly at {broken}")

# --- 7. the price list --------------------------------------------------------
print("7. laws and rules")
V3 = list(itertools.product(V, repeat=3))
laws_alive = {
    "modus ponens (semantic)": all(not (p == T and I(p, q) == T) or q == T for p, q, _ in V3),
    "non-contradiction": all(N(A(p, N(p))) == T for p in V),
    "transitivity of →": all(not (I(p, q) == T and I(q, r) == T) or I(p, r) == T for p, q, r in V3),
    "∧ comm": all(A(p, q) == A(q, p) for p, q, _ in V3),
    "∨ comm": all(O(p, q) == O(q, p) for p, q, _ in V3),
    "∧ assoc": all(A(A(p, q), r) == A(p, A(q, r)) for p, q, r in V3),
    "∨ assoc": all(O(O(p, q), r) == O(p, O(q, r)) for p, q, r in V3),
    "∧ over ∨": all(A(p, O(q, r)) == O(A(p, q), A(p, r)) for p, q, r in V3),
    "∨ over ∧": all(O(p, A(q, r)) == A(O(p, q), O(p, r)) for p, q, r in V3),
    "→ def": all(I(p, q) == O(N(p), q) for p, q, _ in V3),
    "⊕ def": all(X(p, q) == O(A(p, N(q)), A(N(p), q)) for p, q, _ in V3),
    "↔ def": all(E(p, q) == O(A(p, q), A(N(p), N(q))) for p, q, _ in V3),
}
laws_fallen = {
    "¬¬p=p": all(N(N(p)) == p for p in V),
    "De Morgan 1": all(N(A(p, q)) == O(N(p), N(q)) for p, q, _ in V3),
    "De Morgan 2": all(N(O(p, q)) == A(N(p), N(q)) for p, q, _ in V3),
    "contraposition law": all(I(p, q) == I(N(q), N(p)) for p, q, _ in V3),
    "⊕=¬↔": all(X(p, q) == N(E(p, q)) for p, q, _ in V3),
    "∧ idem": all(A(p, p) == p for p in V),
    "∨ idem": all(O(p, p) == p for p in V),
    "absorption": all(A(p, O(p, q)) == p for p, q, _ in V3),
    "p∧T=p": all(A(p, T) == p for p in V),
    "p∨F=p": all(O(p, F) == p for p in V),
    "excluded middle": all(O(p, N(p)) == T for p in V),
    "p→p": all(I(p, p) == T for p in V),
    "Peirce": all(I(I(I(p, q), p), p) == T for p, q, _ in V3),
    "q→(p→q)": all(I(q, I(p, q)) == T for p, q, _ in V3),
}
check(all(laws_alive.values()) and len(laws_alive) == 12, f"12 laws alive: {sum(laws_alive.values())}")
check(not any(laws_fallen.values()) and len(laws_fallen) == 14, f"14 laws fallen: {sum(not v for v in laws_fallen.values())}")
D = lambda x: x == T                                            # noqa: E731
rules = {
    "MP": all(not (D(p) and D(I(p, q))) or D(q) for p, q, _ in V3),
    "MT": all(not (D(I(p, q)) and D(N(q))) or D(N(p)) for p, q, _ in V3),
    "contraposition rule": all(not D(I(p, q)) or D(I(N(q), N(p))) for p, q, _ in V3),
    "disj syllogism": all(not (D(O(p, q)) and D(N(p))) or D(q) for p, q, _ in V3),
    "∧-intro": all(not (D(p) and D(q)) or D(A(p, q)) for p, q, _ in V3),
    "∧-elim": all(not D(A(p, q)) or D(p) for p, q, _ in V3),
    "∨-intro": all(not D(p) or D(O(p, q)) for p, q, _ in V3),
    "¬¬-intro": all(not D(p) or D(N(N(p))) for p in V),
    "transitivity": all(not (D(I(p, q)) and D(I(q, r))) or D(I(p, r)) for p, q, r in V3),
    "K-rule": all(not D(q) or D(I(p, q)) for p, q, _ in V3),
    "explosion": all(not (D(p) and D(N(p))) or D(q) for p, q, _ in V3),
    "resolution": all(not (D(O(p, q)) and D(O(N(p), r))) or D(O(q, r)) for p, q, r in V3),
    "¬¬-elim": all(not D(N(N(p))) or D(p) for p in V),
    "tautology in conclusion": all(not D(p) or D(O(q, N(q))) for p, q, _ in V3),
}
alive = [k for k, v in rules.items() if v]
fallen = [k for k, v in rules.items() if not v]
check(len(alive) == 12 and fallen == ["¬¬-elim", "tautology in conclusion"],
      f"rules: {len(alive)} alive, fallen = {fallen}")

print()
if failures:
    print(f"CORE CHECKS RED — {len(failures)} claim(s) not reproduced:")
    for f in failures:
        print("   ", f)
    sys.exit(1)
print("CORE CHECKS GREEN — every number in paper/ZTL-core-logic.tex reproduced.")
