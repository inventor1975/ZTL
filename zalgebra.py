# -*- coding: utf-8 -*-
"""
Expedition E14: the algebraic passport — completeness as a logic.

The chain, measured totally:
  1. J-OPERATORS from fallen laws: J_T(p) = p∧p (fallen idempotence IS
     the truth detector), J_F(p) = ¬p∧¬p, J_Z(p) = ¬(p↔p) = isZ.
  2. EXPRESSIVE COMPLETENESS of the external layer: every external
     function V^n → {T,F} is a DNF of J-indicators (n = 1, 2 totally).
  3. FULL DEDUCTION THEOREM for the definable external implication
     E(p,q) = ¬(p∧p) ∨ (q∧q): Γ,A ⊨ B ⟺ Γ ⊨ E(A,B) — both ways
     (the primitive → stays one-way: the zero-trust arrow is a verdict,
     E is the meta-level "if p is true then q is true" made internal).
  4. BLOK–PIGOZZI CONDITIONS for algebraizability, on the matrix:
     Δ(p,q) = same-value detector; (i) ⊨Δ(p,p), (ii) detachment,
     (iii) congruence for all six connectives, (iv) p ⊣⊨ Δ(δ(p),ε(p))
     with defining equation δ(p) ≈ ε(p): p∧p ≈ ¬(p∧¬p).
     ⟹ ZTL is algebraizable (BP 1989, Thm 4.7). Kinship: Bochvar's
     external logic is algebraizable via Bochvar algebras BCA
     (Bonzio–Pra Baldi, RSL 2024) — we verify, not inherit.
  5. NOT SELF-EXTENSIONAL: p ⊣⊨ p∧p yet ¬(p∧p) ⊭ ¬p —
     interderivability is not a congruence (idempotence: dead as a law,
     alive as interderivability, and its corpse is the J_T detector).
  6. STRUCTURALITY: the substitution lemma — ⊨ is closed under uniform
     substitution (measured on the pool × a set of substitutions).
"""

from itertools import product

from ztl import T, F, Z, VALUES, NOT, AND, OR, IMP, XOR, XNOR, OPS2, \
    ev, atoms, all_envs, isZ
from entailment import entails, RULES as RULE_BATTERY

p, q, r = "p", "q", "r"


# ---------------------------------------------------------- 1. J-operators
def jT(x):
    return AND(x, x)


def jF(x):
    return AND(NOT(x), NOT(x))


def jZ(x):
    return isZ(x)


def measure_indicators():
    print("### 1. J-operators grown from fallen laws")
    print("  J_T(p) = p∧p (fallen idempotence!), J_F(p) = ¬p∧¬p, J_Z = ¬(p↔p)")
    print(f"  {'x':3s} {'J_T':4s} {'J_F':4s} {'J_Z':4s}")
    ok = True
    for x in VALUES:
        vals = (jT(x), jF(x), jZ(x))
        expect = {T: (T, F, F), F: (F, T, F), Z: (F, F, T)}[x]
        ok &= vals == expect
        print(f"  {x:3s} {vals[0]:4s} {vals[1]:4s} {vals[2]:4s}")
    print(f"  three disjoint exact indicators: {'✓ total' if ok else '✗'}\n")
    return ok


# ------------------------------------- 2. expressive completeness (n=1,2)
def dnf1(table):
    """Unary external function (dict V→{T,F}) as a J-DNF value function."""
    def f(x):
        acc = F
        for c in VALUES:
            if table[c] == T:
                ind = {T: jT, F: jF, Z: jZ}[c]
                acc = OR(acc, ind(x))
        return acc
    return f


def dnf2(table):
    """Binary external function (dict (V,V)→{T,F}) as a J-DNF."""
    def f(x, y):
        acc = F
        for (c1, c2), out in table.items():
            if out == T:
                i1 = {T: jT, F: jF, Z: jZ}[c1]
                i2 = {T: jT, F: jF, Z: jZ}[c2]
                acc = OR(acc, AND(i1(x), i2(y)))
        return acc
    return f


def measure_expressive():
    print("### 2. Expressive completeness of the external layer")
    bad1 = 0
    for combo in product((T, F), repeat=3):
        table = dict(zip(VALUES, combo))
        f = dnf1(table)
        if any(f(x) != table[x] for x in VALUES):
            bad1 += 1
    print(f"  unary external functions: 8 of 8 expressed by J-DNF"
          f" ({'✓' if bad1 == 0 else '✗ failures ' + str(bad1)})")
    cells = list(product(VALUES, repeat=2))
    bad2 = 0
    for combo in product((T, F), repeat=9):
        table = dict(zip(cells, combo))
        f = dnf2(table)
        if any(f(x, y) != table[(x, y)] for x, y in cells):
            bad2 += 1
    print(f"  binary external functions: 512 of 512 expressed by J-DNF"
          f" ({'✓' if bad2 == 0 else '✗ failures ' + str(bad2)})")
    print("  ⟹ the basis {¬,∧,∨} generates ALL external functions")
    print("  (Rosser–Turquette J-machinery, grown from ZTL's own primitives)\n")
    return bad1 == 0 and bad2 == 0


# --------------------------------------------- 3. E-implication, full DDT
def E(a, b):
    """External implication as a formula schema over formulas a, b."""
    return ("or", ("not", ("and", a, a)), ("and", b, b))


def measure_ddt():
    print("### 3. The full deduction theorem for E(p,q) = ¬(p∧p) ∨ (q∧q)")
    pool = [p, q, ("not", p), ("and", p, q), ("or", p, q), ("imp", p, q),
            ("xor", p, q), ("xnor", p, q), ("not", ("not", p))]
    gammas = [[], [r], [("or", r, r)], [("imp", p, r)]]
    total = mism_E = mism_imp = 0
    for G in gammas:
        for A in pool:
            for B in pool:
                total += 1
                rule = entails(G + [A], B) is None           # Γ,A ⊨ B
                law_E = entails(G, E(A, B)) is None          # Γ ⊨ E(A,B)
                law_i = entails(G, ("imp", A, B)) is None    # Γ ⊨ A→B
                if rule != law_E:
                    mism_E += 1
                if rule != law_i:
                    mism_imp += 1
    print(f"  checked (Γ, A, B) triples: {total}")
    print(f"  Γ,A ⊨ B  ⟺  Γ ⊨ E(A,B):  divergences {mism_E} "
          f"({'✓ DDT two-way, total' if mism_E == 0 else '✗'})")
    print(f"  Γ,A ⊨ B  ⟺  Γ ⊨ A→B:   divergences {mism_imp} "
          f"(the primitive arrow stays one-way, as measured in the keel)")
    print("  The zero-trust arrow is a verdict to be earned; E internalizes")
    print("  the meta-claim \"if A is true, B is true\" — ⊨ IS internalized,")
    print("  just not by the primitive →.\n")
    return mism_E == 0 and mism_imp > 0


# ------------------------------ 4. Blok–Pigozzi conditions on the matrix
def dEq(a, b):
    """Δ(p,q): the same-value detector, as a value function."""
    return OR(OR(AND(jT(a), jT(b)), AND(jF(a), jF(b))), AND(jZ(a), jZ(b)))


def delta(a, b):
    """Δ as a formula schema."""
    JT = lambda x: ("and", x, x)
    JF = lambda x: ("and", ("not", x), ("not", x))
    JZ = lambda x: ("not", ("xnor", x, x))
    return ("or", ("or", ("and", JT(a), JT(b)), ("and", JF(a), JF(b))),
            ("and", JZ(a), JZ(b)))


def measure_bp():
    print("### 4. Blok–Pigozzi conditions (algebraizability), on the matrix")
    okA = all(dEq(a, b) == (T if a == b else F)
              for a in VALUES for b in VALUES)
    print(f"  Δ is an exact same-value detector: {'✓' if okA else '✗'}")
    ok1 = all(dEq(a, a) == T for a in VALUES)
    print(f"  (i)   reflexivity ⊨ Δ(p,p): {'✓ total' if ok1 else '✗'}")
    ok2 = all(not (a == T and dEq(a, b) == T) or b == T
              for a in VALUES for b in VALUES)
    print(f"  (ii)  detachment p, Δ(p,q) ⊨ q: {'✓ total' if ok2 else '✗'}")
    ok3 = True
    ok3 &= all(dEq(a, b) != T or dEq(NOT(a), NOT(b)) == T
               for a in VALUES for b in VALUES)
    for name, op in OPS2.items():
        for a, b, c, d in product(VALUES, repeat=4):
            if dEq(a, c) == T and dEq(b, d) == T and \
                    dEq(op(a, b), op(c, d)) != T:
                ok3 = False
    print(f"  (iii) congruence for all 6 connectives: "
          f"{'✓ total (¬: 9; binary: 5×81 tuples)' if ok3 else '✗'}")
    # defining equation δ(p) ≈ ε(p):  p∧p ≈ ¬(p∧¬p)
    ok_eq = all((AND(x, x) == NOT(AND(x, NOT(x)))) == (x == T)
                for x in VALUES)
    print(f"  truth equation p∧p ≈ ¬(p∧¬p) holds ⟺ p=T: "
          f"{'✓ total' if ok_eq else '✗'}")
    lhs = lambda x: ("and", x, x)
    rhs = lambda x: ("not", ("and", x, ("not", x)))
    ok4a = entails([p], delta(lhs(p), rhs(p))) is None
    ok4b = entails([delta(lhs(p), rhs(p))], p) is None
    print(f"  (iv)  p ⊣⊨ Δ(p∧p, ¬(p∧¬p)): "
          f"{'✓ both ways' if ok4a and ok4b else '✗'}")
    ok = okA and ok1 and ok2 and ok3 and ok_eq and ok4a and ok4b
    if ok:
        print("  ⟹ ZTL IS ALGEBRAIZABLE (Blok–Pigozzi 1989, Thm 4.7:")
        print("  conditions (i)–(iv) suffice; here verified on the matrix).")
        print("  Kinship: Bochvar's external logic ⇝ Bochvar algebras BCA")
        print("  (Bonzio–Pra Baldi 2024); ZTL grows the witnesses from its")
        print("  own primitives — verified directly, not inherited.\n")
    return ok


# ----------------------------------------- 5. failure of self-extensionality
def measure_selfext():
    print("### 5. Self-extensionality FAILS (and that is a feature)")
    d1 = entails([p], ("and", p, p)) is None
    d2 = entails([("and", p, p)], p) is None
    print(f"  p ⊣⊨ p∧p (interderivable): {'✓' if d1 and d2 else '✗'}")
    cex = entails([("not", ("and", p, p))], ("not", p))
    print(f"  ¬(p∧p) ⊨ ¬p: ✗ fails at "
          f"{', '.join(f'{k}={v}' for k, v in (cex or {}).items())}"
          f" — interderivability is NOT a congruence")
    print("  Idempotence: dead as a law, alive as interderivability — and")
    print("  its corpse is exactly the J_T detector. The same failure that")
    print("  breaks self-extensionality builds the algebra.\n")
    return d1 and d2 and cex is not None


# -------------------------------------------------- 6. structurality of ⊨
def substitute(phi, sigma):
    if isinstance(phi, str):
        if phi in VALUES:
            return phi
        return sigma.get(phi, phi)
    return (phi[0],) + tuple(substitute(x, sigma) for x in phi[1:])


def measure_structural():
    print("### 6. Structurality: ⊨ is closed under uniform substitution")
    sigmas = [
        {p: ("not", q), q: ("and", p, q)},
        {p: ("imp", p, q), q: "Z"},
        {p: ("xnor", p, p), q: ("or", q, ("not", p))},
        {p: q, q: p},
    ]
    # substitution lemma: ev(σφ, v) = ev(φ, v∘σ)
    pool = [p, q, ("not", p), ("and", p, q), ("or", p, ("not", q)),
            ("imp", p, q), ("xor", ("not", p), q), ("xnor", p, q)]
    bad_lemma = 0
    for phi in pool:
        for sigma in sigmas:
            sphi = substitute(phi, sigma)
            for env in all_envs(atoms(sphi) | {p, q}):
                env2 = {a: ev(substitute(a, sigma), env) for a in atoms(phi)}
                if ev(sphi, env) != ev(phi, env2):
                    bad_lemma += 1
    print(f"  substitution lemma ev(σφ,v) = ev(φ,v∘σ): "
          f"{'✓ total on pool×σ' if bad_lemma == 0 else '✗ ' + str(bad_lemma)}")
    bad_ent = 0
    checked = 0
    for name, prems, concl in RULE_BATTERY:
        if entails(prems, concl) is not None:
            continue                       # only alive rules transport
        for sigma in sigmas:
            checked += 1
            if entails([substitute(x, sigma) for x in prems],
                       substitute(concl, sigma)) is not None:
                bad_ent += 1
                print(f"    ✗ {name} broke under σ")
    print(f"  alive battery rules under substitutions ({checked} checks): "
          f"{'✓ all preserved' if bad_ent == 0 else '✗'}")
    print("  ⟹ together with reflexivity/monotonicity/cut (by construction):")
    print("  ⊨ is a STRUCTURAL Tarskian consequence — ZTL is a logic in the")
    print("  full abstract sense; finitary and decidable (finite matrix).\n")
    return bad_lemma == 0 and bad_ent == 0


if __name__ == "__main__":
    print("=" * 72)
    print("E14. THE ALGEBRAIC PASSPORT: ZTL AS A LOGIC, COMPLETED")
    print("=" * 72 + "\n")
    r1 = measure_indicators()
    r2 = measure_expressive()
    r3 = measure_ddt()
    r4 = measure_bp()
    r5 = measure_selfext()
    r6 = measure_structural()
    print("### Summary")
    print("  Fallen idempotence → J_T detector → all external functions →")
    print("  E with a two-way deduction theorem → Δ + truth equation →")
    print("  Blok–Pigozzi conditions → ZTL is ALGEBRAIZABLE; yet not")
    print("  self-extensional, and the primitive → keeps its one-way DDT.")
    print("  The fallen laws paid for the algebra.")
    if not all((r1, r2, r3, r4, r5, r6)):
        raise SystemExit("A MEASUREMENT FAILED — stop.")
