# -*- coding: utf-8 -*-
"""
ZTL identity auditor: brute force over all value assignments.

Two kinds of checks:
  * equality of two formulas (values coincide on all assignments);
  * validity of a formula (value T on all assignments).
Plus semantic modus ponens.

Every fallen law is not a bug but a line of the manifesto: the price of
the principle "truth is not granted on credit". The alive/fallen list
prints as MEASURED.
"""

from ztl import T, F, Z, VALUES, ev, atoms, all_envs, show

# --- identity catalogue: (name, left formula, right formula) ---
p, q, r = "p", "q", "r"

EQUALITIES = [
    ("double negation        ¬¬p = p",            ("not", ("not", p)), p),
    ("De Morgan 1            ¬(p∧q) = ¬p∨¬q",     ("not", ("and", p, q)), ("or", ("not", p), ("not", q))),
    ("De Morgan 2            ¬(p∨q) = ¬p∧¬q",     ("not", ("or", p, q)), ("and", ("not", p), ("not", q))),
    ("contraposition         p→q = ¬q→¬p",        ("imp", p, q), ("imp", ("not", q), ("not", p))),
    ("implication via ∨      p→q = ¬p∨q",         ("imp", p, q), ("or", ("not", p), q)),
    ("⊕ in distributive form p⊕q = (p∧¬q)∨(¬p∧q)", ("xor", p, q), ("or", ("and", p, ("not", q)), ("and", ("not", p), q))),
    ("↔ in distributive form p↔q = (p∧q)∨(¬p∧¬q)", ("xnor", p, q), ("or", ("and", p, q), ("and", ("not", p), ("not", q)))),
    ("⊕ as negation of ↔     p⊕q = ¬(p↔q)",       ("xor", p, q), ("not", ("xnor", p, q))),
    ("↔ via two implications p↔q = (p→q)∧(q→p)",  ("xnor", p, q), ("and", ("imp", p, q), ("imp", q, p))),
    ("commutativity of ∧     p∧q = q∧p",          ("and", p, q), ("and", q, p)),
    ("commutativity of ∨     p∨q = q∨p",          ("or", p, q), ("or", q, p)),
    ("associativity of ∧     (p∧q)∧r = p∧(q∧r)",  ("and", ("and", p, q), r), ("and", p, ("and", q, r))),
    ("associativity of ∨     (p∨q)∨r = p∨(q∨r)",  ("or", ("or", p, q), r), ("or", p, ("or", q, r))),
    ("distributivity ∧/∨     p∧(q∨r) = (p∧q)∨(p∧r)", ("and", p, ("or", q, r)), ("or", ("and", p, q), ("and", p, r))),
    ("distributivity ∨/∧     p∨(q∧r) = (p∨q)∧(p∨r)", ("or", p, ("and", q, r)), ("and", ("or", p, q), ("or", p, r))),
    ("idempotence of ∧       p∧p = p",            ("and", p, p), p),
    ("idempotence of ∨       p∨p = p",            ("or", p, p), p),
    ("absorption             p∧(p∨q) = p",        ("and", p, ("or", p, q)), p),
    ("unit of ∧              p∧T = p",            ("and", p, "T"), p),
    ("unit of ∨              p∨F = p",            ("or", p, "F"), p),
]

VALIDITIES = [
    ("excluded middle        p∨¬p",               ("or", p, ("not", p))),
    ("non-contradiction      ¬(p∧¬p)",            ("not", ("and", p, ("not", p)))),
    ("reflexivity of →       p→p",                ("imp", p, p)),
    ("transitivity of →      ((p→q)∧(q→r))→(p→r)", ("imp", ("and", ("imp", p, q), ("imp", q, r)), ("imp", p, r))),
    ("Peirce's law           ((p→q)→p)→p",        ("imp", ("imp", ("imp", p, q), p), p)),
    ("affirm the consequent  q→(p→q)",            ("imp", q, ("imp", p, q))),
]


def check_equality(lhs, rhs):
    """List of assignments on which the formulas diverge."""
    names = atoms(lhs) | atoms(rhs)
    fails = []
    for env in all_envs(names):
        a, b = ev(lhs, env), ev(rhs, env)
        if a != b:
            fails.append((env, a, b))
    return fails


def check_validity(phi):
    """List of assignments on which the formula is not T."""
    fails = []
    for env in all_envs(atoms(phi)):
        v = ev(phi, env)
        if v != T:
            fails.append((env, v))
    return fails


def check_modus_ponens():
    """Semantic MP: wherever v(A)=T and v(A→B)=T, v(B)=T must hold.
    Checked on all pairs of depth<=1 formulas over atoms p,q — including
    cases where the premises contain Z."""
    from itertools import product
    small = [p, q, ("not", p), ("not", q), ("and", p, q), ("or", p, q),
             ("imp", p, q), ("xor", p, q), ("xnor", p, q), "T", "F", "Z"]
    fails = []
    for A, B in product(small, repeat=2):
        names = atoms(A) | atoms(B)
        for env in all_envs(names):
            if ev(A, env) == T and ev(("imp", A, B), env) == T and ev(B, env) != T:
                fails.append((show(A), show(B), env))
    return fails


def check_eager_theorem():
    """Greediness theorem: no COMPOUND formula ever takes the value Z.
    Checked on all depth-2 formulas over p,q."""
    forms = [p, q, ("not", p)]
    depth2 = []
    for opn in ("and", "or", "imp", "xor", "xnor"):
        for a in forms:
            for b in forms:
                depth2.append((opn, a, b))
    depth2 += [("not", f) for f in depth2[:]]
    bad = []
    for phi in depth2:
        for env in all_envs(atoms(phi)):
            if ev(phi, env) == Z:
                bad.append((show(phi), env))
    return bad


def run_audit():
    print("=" * 72)
    print("ZTL IDENTITY AUDIT (brute force over all T/F/Z assignments)")
    print("=" * 72)

    alive, dead = [], []
    for name, lhs, rhs in EQUALITIES:
        fails = check_equality(lhs, rhs)
        (alive if not fails else dead).append((name, fails))
    for name, phi in VALIDITIES:
        fails = check_validity(phi)
        (alive if not fails else dead).append((name + "  [validity]", fails))

    print("\n-- ALIVE LAWS --")
    for name, _ in alive:
        print("  ✓ " + name)

    print("\n-- FALLEN LAWS (the price of the principle; first counterexample) --")
    for name, fails in dead:
        env = fails[0][0]
        env_s = ", ".join(f"{k}={v}" for k, v in sorted(env.items()))
        got = fails[0][1:]
        print(f"  ✗ {name}   [{env_s} → {' vs '.join(got)}]")

    mp = check_modus_ponens()
    print("\n-- MODUS PONENS (semantic) --")
    if not mp:
        print("  ✓ holds: v(A)=T and v(A→B)=T imply v(B)=T everywhere")
    else:
        print(f"  ✗ fails, counterexamples: {len(mp)}; first: {mp[0]}")

    eager = check_eager_theorem()
    print("\n-- GREEDINESS THEOREM --")
    if not eager:
        print("  ✓ confirmed: compound formulas never take the value Z")
    else:
        print(f"  ✗ violated: {eager[0]}")

    print(f"\nTotal: alive {len(alive)}, fallen {len(dead)}.")
    return alive, dead


if __name__ == "__main__":
    run_audit()
