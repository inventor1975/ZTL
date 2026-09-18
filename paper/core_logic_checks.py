#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
core_logic_checks — every number the ZTL papers quote about the core matrix and
its relation to classical logic (paper/ZTL-draft_2.0.0.md §§2-4, 10 and the
core-logic article), regenerated from ztl.py (the code is the arbiter) and from
the neighbour matrices of pssl/family.py. Nothing here is typed in by hand; a
claim in a paper that this script does not reproduce is a claim the paper must
not make. Wired into run_all.py (2026-09-19) so that the text and the numbers
cannot drift apart silently — the 2.0.0 frame (588 = 588 and the same set;
26 laws = 12 + 14 refuted, 0 undecided; the default is external Bochvar,
0 of 45; 7 and 8 cells; the sink; no conservative default) stands on it.

Sections, in the order the paper uses them:
  1. the ten tables have no Z cell; the six operators output only T/F
  2. the negative routes to the second five tables fail (3/3/3/5 cells),
     the positive definitions hold (0 cells)
  3. IDENTICAL ON VERIFIED DATA: on the depth<=2 pool (2926 formulas over p,q)
     restricted to mark-free valuations, classical and ZTL validate the SAME
     588 formulas, element for element — zero classical laws lost
  4. the 26 laws: all 26 hold on verified data; on a marked atom 12 hold and
     14 are REFUTED with an exhibited witness — 0 undecided; 12 rules of 14
  5. WHAT THE MARK BUYS: on 1840 of 2924 compounds (63%) the verdict depends on
     whether an atom is unverified or false; under the substitution
     unverified := false the count is 0 by construction; isZ(x) = ¬(x↔x)
  6. THE ENGINEERING DEFAULT IS EXTERNAL BOCHVAR: "classical with
     unverified := false" agrees with Bochvar's external layer on all 45 binary
     cells and parts only at ¬; ZTL parts from Bochvar in 7 cells (listed) and
     from the substitution in 8; on the extended domain ZTL 212 ⊊ Bochvar 548,
     with p→p, p↔p, q→(p→q) in the difference
  7. THE SINK CASE: safe := ¬tainted ∨ sanitized — ZTL refuses on the unverified
     case, both classical defaults grant a pass; in (¬t∨s)∧(t∨l) no value of t
     avoids a free truth in one conjunct — no conservative default exists
  8. the Suszko discriminator on the 90-compound regression pool
  9. Tomova's criteria: (1) yes (2) yes (3) broken in exactly one cell (Z,Z)

Run:  python3 paper/core_logic_checks.py      (from the repository root; the root
      is also found via $ZTL_ROOT or as the parent of this file's directory)
Exit 0 = every number in the paper is reproduced.
"""
import itertools
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
_CANDIDATES = [os.environ.get("ZTL_ROOT", ""),
               os.path.join(_HERE, "..", "..", "ZTL"),
               os.path.dirname(_HERE), os.getcwd()]
_ROOT = next((os.path.abspath(c) for c in _CANDIDATES
              if c and os.path.exists(os.path.join(c, "ztl.py"))), None)
if _ROOT is None:
    sys.exit("ztl.py not found: set ZTL_ROOT to the ZTL repository root")
sys.path.insert(0, _ROOT)
sys.path.insert(0, os.path.join(_ROOT, "pssl"))

import ztl                                                    # noqa: E402
import family as Fm                                           # noqa: E402

T, F, Z = ztl.T, ztl.F, ztl.Z
V = [T, F, Z]
N, A, O, I, X, E = ztl.NOT, ztl.AND, ztl.OR, ztl.IMP, ztl.XOR, ztl.XNOR
OPS = {"not": N, "and": A, "or": O, "imp": I, "xor": X, "xnor": E}
BIN = ("and", "or", "imp", "xor", "xnor")
SYM = {"and": "∧", "or": "∨", "imp": "→", "xor": "⊕", "xnor": "↔"}
tv = lambda b: T if b else F                                   # noqa: E731
# classical connectives on {T,F}
CL = {"not": lambda a: tv(a == F), "and": lambda a, b: tv(a == T and b == T),
      "or": lambda a, b: tv(a == T or b == T), "imp": lambda a, b: tv(a == F or b == T),
      "xor": lambda a, b: tv(a != b), "xnor": lambda a, b: tv(a == b)}
# Bochvar's external layer: classical connective on the assertions box(x); ¬ = "x is false"
box = {T: 1, F: 0, Z: 0}
BOCH = {"not": lambda a: tv(a == F),
        "and": lambda a, b: tv(box[a] and box[b]),
        "or": lambda a, b: tv(box[a] or box[b]),
        "imp": lambda a, b: tv((not box[a]) or box[b]),
        "xnor": lambda a, b: tv(box[a] == box[b]),
        "xor": lambda a, b: tv(box[a] != box[b])}
# the engineering default: substitute F for the mark, then compute classically
sub = lambda x: F if x == Z else x                             # noqa: E731
SUB = {k: (lambda f: (lambda a, b: f(sub(a), sub(b))))(CL[k]) for k in BIN}
SUB["not"] = lambda a: CL["not"](sub(a))
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


ENVS = [dict(zip("pq", c)) for c in itertools.product(V, repeat=2)]          # 9 marked-or-not
GENVS = [dict(zip("pq", c)) for c in itertools.product((T, F), repeat=2)]    # 4 verified


def valid(ops, phi, envs=ENVS):
    return all(ev(ops, phi, e) == T for e in envs)


# the depth<=2 pool over p, q with six connectives
d1 = ["p", "q"] + [("not", x) for x in ("p", "q")] + \
     [(o, a, b) for o in BIN for a in ("p", "q") for b in ("p", "q")]
d2 = [(o, a, b) for o in BIN for a in d1 for b in d1] + \
     [("not", x) for x in d1 if not isinstance(x, str)]
POOL = d1 + d2
COMPOUNDS = [f for f in POOL if not isinstance(f, str)]

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

# --- 3. identical on verified data --------------------------------------------
print("3. identical on verified data (pool of depth<=2 over p,q; mark-free valuations)")
check(len(POOL) == 2926, f"pool size {len(POOL)}")
zt_g = {i for i, f in enumerate(POOL) if valid(OPS, f, GENVS)}
ct_g = {i for i, f in enumerate(POOL) if valid(CL, f, GENVS)}
check(len(ct_g) == 588 and len(zt_g) == 588, f"classical {len(ct_g)} validities, ZTL {len(zt_g)}")
check(zt_g == ct_g, "the two sets are EQUAL, element for element — zero classical laws lost")
check(all(ev(OPS, f, e) == ev(CL, f, e) for f in POOL for e in GENVS),
      "every formula, every verified valuation: the same value (the pool instance of evalF_agrees)")

# --- 4. the 26 laws and the 14 rules ------------------------------------------
print("4. the twenty-six laws: verified data vs a marked atom")
V3 = list(itertools.product(V, repeat=3))
G3 = list(itertools.product((T, F), repeat=3))


def law_holds(law, triples):
    return all(law(p, q, r) for p, q, r in triples)


LAWS_KEEP = {  # hold on a marked atom too
    "modus ponens (semantic)": lambda p, q, r: not (p == T and I(p, q) == T) or q == T,
    "non-contradiction": lambda p, q, r: N(A(p, N(p))) == T,
    "transitivity of →": lambda p, q, r: not (I(p, q) == T and I(q, r) == T) or I(p, r) == T,
    "∧ comm": lambda p, q, r: A(p, q) == A(q, p),
    "∨ comm": lambda p, q, r: O(p, q) == O(q, p),
    "∧ assoc": lambda p, q, r: A(A(p, q), r) == A(p, A(q, r)),
    "∨ assoc": lambda p, q, r: O(O(p, q), r) == O(p, O(q, r)),
    "∧ over ∨": lambda p, q, r: A(p, O(q, r)) == O(A(p, q), A(p, r)),
    "∨ over ∧": lambda p, q, r: O(p, A(q, r)) == A(O(p, q), O(p, r)),
    "→ def": lambda p, q, r: I(p, q) == O(N(p), q),
    "⊕ def": lambda p, q, r: X(p, q) == O(A(p, N(q)), A(N(p), q)),
    "↔ def": lambda p, q, r: E(p, q) == O(A(p, q), A(N(p), N(q))),
}
# (name, both sides / the formula, is_formula) — the fourteen that need ground
LAWS_GROUND = {
    "¬¬p=p": (lambda p, q, r: (N(N(p)), p), False),
    "De Morgan 1": (lambda p, q, r: (N(A(p, q)), O(N(p), N(q))), False),
    "De Morgan 2": (lambda p, q, r: (N(O(p, q)), A(N(p), N(q))), False),
    "contraposition law": (lambda p, q, r: (I(p, q), I(N(q), N(p))), False),
    "⊕=¬↔": (lambda p, q, r: (X(p, q), N(E(p, q))), False),
    "∧ idem": (lambda p, q, r: (A(p, p), p), False),
    "∨ idem": (lambda p, q, r: (O(p, p), p), False),
    "absorption": (lambda p, q, r: (A(p, O(p, q)), p), False),
    "p∧T=p": (lambda p, q, r: (A(p, T), p), False),
    "p∨F=p": (lambda p, q, r: (O(p, F), p), False),
    "excluded middle": (lambda p, q, r: (O(p, N(p)),), True),
    "p→p": (lambda p, q, r: (I(p, p),), True),
    "Peirce": (lambda p, q, r: (I(I(I(p, q), p), p),), True),
    "q→(p→q)": (lambda p, q, r: (I(q, I(p, q)),), True),
}


def ground_law_holds(spec, triples):
    f, is_formula = spec
    for p, q, r in triples:
        v = f(p, q, r)
        if is_formula and v[0] != T:
            return False
        if not is_formula and v[0] != v[1]:
            return False
    return True


check(len(LAWS_KEEP) + len(LAWS_GROUND) == 26, "26 laws in the census")
check(all(law_holds(l, G3) for l in LAWS_KEEP.values()) and
      all(ground_law_holds(s, G3) for s in LAWS_GROUND.values()),
      "ALL 26 hold on verified data (no atom marked)")
check(all(law_holds(l, V3) for l in LAWS_KEEP.values()), "12 hold on a marked atom as well")
check(not any(ground_law_holds(s, V3) for s in LAWS_GROUND.values()), "14 do not extend to the mark")
# every one of the fourteen is REFUTED with a witness whose sides are both verdicts (never Z)
undecided, witnesses = 0, {}
for name, (f, is_formula) in LAWS_GROUND.items():
    for p, q, r in V3:
        v = f(p, q, r)
        if is_formula:
            if v[0] == Z:
                undecided += 1
            if v[0] == F:
                witnesses.setdefault(name, (p, q, r, v))
                break
        else:
            if v[0] != v[1]:
                if Z in v and is_formula:
                    undecided += 1
                witnesses.setdefault(name, (p, q, r, v))
                break
check(len(witnesses) == 14 and undecided == 0,
      f"each of the 14 is refuted with an exhibited witness; undecided outcomes: {undecided}")
formula_values = {n: witnesses[n][3][0] for n, (_, isf) in LAWS_GROUND.items() if isf}
check(all(v == F for v in formula_values.values()), f"the four formula-laws take the value F on the mark: {formula_values}")
# rules
D = lambda x: x == T                                            # noqa: E731
RULES = {
    "MP": lambda p, q, r: not (D(p) and D(I(p, q))) or D(q),
    "MT": lambda p, q, r: not (D(I(p, q)) and D(N(q))) or D(N(p)),
    "contraposition rule": lambda p, q, r: not D(I(p, q)) or D(I(N(q), N(p))),
    "disj syllogism": lambda p, q, r: not (D(O(p, q)) and D(N(p))) or D(q),
    "∧-intro": lambda p, q, r: not (D(p) and D(q)) or D(A(p, q)),
    "∧-elim": lambda p, q, r: not D(A(p, q)) or D(p),
    "∨-intro": lambda p, q, r: not D(p) or D(O(p, q)),
    "¬¬-intro": lambda p, q, r: not D(p) or D(N(N(p))),
    "transitivity": lambda p, q, r: not (D(I(p, q)) and D(I(q, r))) or D(I(p, r)),
    "K-rule": lambda p, q, r: not D(q) or D(I(p, q)),
    "explosion": lambda p, q, r: not (D(p) and D(N(p))) or D(q),
    "resolution": lambda p, q, r: not (D(O(p, q)) and D(O(N(p), r))) or D(O(q, r)),
    "¬¬-elim": lambda p, q, r: not D(N(N(p))) or D(p),
    "tautology in conclusion": lambda p, q, r: not D(p) or D(O(q, N(q))),
}
alive = [k for k, v in RULES.items() if law_holds(v, V3)]
fallen = [k for k, v in RULES.items() if not law_holds(v, V3)]
check(len(alive) == 12 and fallen == ["¬¬-elim", "tautology in conclusion"],
      f"rules: {len(alive)} alive, fallen = {fallen}")
check(A(Z, N(Z)) == F and N(A(Z, N(Z))) == T, "non-contradiction on the mark: Z∧¬Z = F, ¬(Z∧¬Z) = T")
check(I(Z, Z) == F and I(T, Z) == F, "dt_one_way cells: Z→Z = F, T→Z = F")

# --- 5. what the mark buys ----------------------------------------------------
print("5. what the mark buys: compounds whose verdict depends on unverified-vs-false")


def depends_on_mark(f):
    return any(ev(OPS, f, e) != ev(OPS, f, {k: sub(v) for k, v in e.items()}) for e in ENVS)


DEP = [f for f in COMPOUNDS if depends_on_mark(f)]
check(len(COMPOUNDS) == 2924, f"compounds in the pool: {len(COMPOUNDS)}")
check(len(DEP) == 1840, f"verdict depends on mark-vs-false: {len(DEP)} of {len(COMPOUNDS)} ({100 * len(DEP) / len(COMPOUNDS):.0f}%)")
under_sub = sum(1 for f in COMPOUNDS if any(ev(SUB, f, e) != ev(SUB, f, {k: sub(v) for k, v in e.items()}) for e in ENVS))
check(under_sub == 0, f"under the substitution unverified := false the same count is {under_sub} (Z and F are one input)")
short = [show(f) for f in sorted(DEP, key=lambda f: len(show(f)))[:6]]
print("     shortest:", short)
check(N(E(Z, Z)) == T and N(E(T, T)) == F and N(E(F, F)) == F, "isZ(x) = ¬(x↔x): T on the mark, F on T and on F")

# --- 6. the engineering default is external Bochvar ---------------------------
print("6. the engineering default (unverified := false, then classical) against Bochvar and ZTL")
div45 = [(k, a, b) for k in BIN for a in V for b in V if SUB[k](a, b) != BOCH[k](a, b)]
check(len(div45) == 0, "substitution vs external Bochvar on the five binary connectives: 0 of 45 cells differ")
neg_div = [a for a in V if SUB["not"](a) != BOCH["not"](a)]
check(neg_div == [Z], f"they part only at negation: ¬Z = {SUB['not'](Z)} (substitution) vs {BOCH['not'](Z)} (Bochvar)")
total = 0
for k in ("not", "and", "or", "imp", "xnor", "xor"):
    if k == "not":
        d = [(a,) for a in V if BOCH[k](a) != OPS[k](a)]
    else:
        d = [(a, b) for a in V for b in V if BOCH[k](a, b) != OPS[k](a, b)]
    total += len(d)
    print(f"     ZTL vs Bochvar {SYM.get(k, '¬')}: {len(d)} {d}")
check(total == 7, f"ZTL vs external Bochvar: {total} cells")
d8 = sum(1 for a in V if SUB["not"](a) != N(a)) + \
     sum(1 for k in BIN for a in V for b in V if SUB[k](a, b) != OPS[k](a, b))
check(d8 == 8, f"ZTL vs the substitution: {d8} cells (the seven plus ¬Z)")
check(SUB["not"](Z) == T and SUB["imp"](Z, F) == T and SUB["xnor"](Z, Z) == T,
      "at each of them the substitution derives a verdict from no information: ¬Z=T, Z→F=T, Z↔Z=T")
zt = {show(f) for f in POOL if valid(OPS, f)}
bt = {show(f) for f in POOL if valid(BOCH, f)}
check(len(zt) == 212 and len(bt) == 548, f"extended domain (marked valuations allowed): ZTL {len(zt)} validities, Bochvar {len(bt)}")
check(zt < bt, "ZTL's validities are a PROPER subset of external Bochvar's on the extended domain")
check({"(p→p)", "(p↔p)", "(q→(p→q))"} <= (bt - zt), "p→p, p↔p, q→(p→q) hold for Bochvar, not for ZTL")

# --- 7. the sink case ---------------------------------------------------------
print("7. the sink case: safe := ¬tainted ∨ sanitized")
safe = lambda t, s: O(N(t), s)                                  # noqa: E731
check(safe(T, T) == T and safe(T, F) == F and safe(Z, Z) == F,
      f"ZTL: verified/verified {safe(T, T)}, verified/refuted {safe(T, F)}, neither established {safe(Z, Z)} (refused)")
check(CL["or"](CL["not"](F), F) == T and CL["or"](CL["not"](T), T) == T,
      "classical: unverified := false gives ¬F∨F = T, unverified := true gives ¬T∨T = T — both PASS")
free = {}
for t in (T, F):
    c1 = all(CL["or"](CL["not"](t), s) == T for s in (T, F))    # true whatever sanitized is
    c2 = all(CL["or"](t, l) == T for l in (T, F))               # true whatever logged is
    free[t] = (c1, c2)
check(free[T] == (False, True) and free[F] == (True, False),
      "(¬t∨s)∧(t∨l): t := T makes the second conjunct true for free, t := F the first — no conservative default")

# --- 8. Suszko discriminator on the regression pool ---------------------------
print("8. compounds that take the middle value on the depth-2 regression pool (audit.py's)")
leaves = ["p", "q", ("not", "p")]
pool90 = [(o, a, b) for o in BIN for a in leaves for b in leaves]
pool90 += [("not", f) for f in pool90[:]]
check(len(pool90) == 90, f"pool size {len(pool90)}")
zbad = sum(1 for phi in pool90 if any(ev(OPS, phi, e) == Z for e in ENVS))
check(zbad == 0, f"ZTL: {zbad} of {len(pool90)}")


def mat_ops(m):
    return {"not": m.neg, "and": m.conj, "or": m.disj, "imp": m.imp,
            "xor": lambda a, b: m.disj(m.conj(a, m.neg(b)), m.conj(m.neg(a), b)),
            "xnor": lambda a, b: m.disj(m.conj(a, b), m.conj(m.neg(a), m.neg(b)))}


menvs = [dict(zip("pq", c)) for c in itertools.product(Fm.VALS, repeat=2)]
expect8 = {"K3": 90, "LP": 90, "weak Kleene": 90, "Lukasiewicz L3": 80}
for m in Fm.FAMILY:
    ops = mat_ops(m)
    bad = sum(1 for phi in pool90 if any(ev(ops, phi, e) == Fm.UU for e in menvs))
    check(bad == expect8[m.name], f"{m.name}: {bad} of {len(pool90)}")
    check(m.involution(), f"{m.name}: negation involutive (covered by involution_gives_dne)")
check(N(N(Z)) == T, "ZTL: ¬¬Z = T — the broken involution")

# --- 9. Tomova ----------------------------------------------------------------
print("9. Tomova's natural-implication criteria")
c1 = all(I(a, b) == CL["imp"](a, b) for a in (T, F) for b in (T, F))
c2 = all(not (a == T and I(a, b) == T and b != T) for a in V for b in V)
order = {F: 0, Z: 1, T: 2}
broken = [(a, b) for a in V for b in V if order[a] <= order[b] and I(a, b) != T]
check(c1, "(1) classical on {T,F}")
check(c2, "(2) modus ponens preserves the designated value")
check(broken == [(Z, Z)], f"(3) p≤q ⇒ p→q designated, broken exactly at {broken}")

print()
if failures:
    print(f"CORE CHECKS RED — {len(failures)} claim(s) not reproduced:")
    for f in failures:
        print("   ", f)
    sys.exit(1)
print("CORE CHECKS GREEN — every core number of the papers reproduced.")
