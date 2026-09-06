# -*- coding: utf-8 -*-
"""
Expedition E55: SYNTACTIC cut elimination — the procedure run on trees, and
its bound measured against what it actually produces.

`lean/ZCutElim.lean` proves, on the empty axiom list, that a derivation of
`S, T:φ` with k₁ leaves and one of `S, N:φ` with k₂ leaves can be turned into
a derivation of `S` with at most `B0 true k₁ k₂ (basis φ)` leaves — by
inversions, weakenings and smaller cuts, never through a model. A Prop-level
theorem carries no program, so this file is the SAME procedure written as one:
derivation trees, the same operations, the same recursion, and a checker that
re-verifies every tree it builds against the rules.

Measured on the E16 pool (zsequent.py): for every (S, φ) where both premises
close in the engine (head-first, exactly `TableauCert.closes`):
  k₁, k₂  = leaves of the engine's own derivations of the two premises;
  k       = leaves of what the PROCEDURE returns for S;
  B       = B0 true k₁ k₂ (basis φ), the proved bound;
  k₀      = leaves of the engine's direct derivation of S (no cut at all).
Three questions, each answered by a number and not by an argument:
  (1) k ≤ B on every instance — the bound holds on the twin;
  (2) how tight: max k/B, and how often k = B;
  (3) the price of the procedure against plain search: max k/k₀ — and the
      other way round, whether a cut ever SHORTENS: any k₀ > k₁ + k₂?
"""
from tableau import ST, SF, SP, SN, CLASSIC
from ztl import T, F, Z, VALUES
from zsequent import pool_formulas, pool_sequents

ALL = frozenset(VALUES)

# ---------------------------------------------------------------- formulas
def basis(phi):
    if isinstance(phi, str):
        return phi
    op = phi[0]
    if op == "not":
        return ("not", basis(phi[1]))
    a, b = basis(phi[1]), basis(phi[2])
    if op == "and":
        return ("and", a, b)
    if op == "or":
        return ("or", a, b)
    if op == "imp":
        return ("or", ("not", a), b)
    if op == "xor":
        return ("or", ("and", a, ("not", b)), ("and", ("not", a), b))
    if op == "xnor":
        return ("or", ("and", a, b), ("and", ("not", a), ("not", b)))
    raise ValueError(op)

def B0(pol, k1, k2, phi):
    """The bound, exactly as `ZCut.B0` (on basis formulas)."""
    if isinstance(phi, str):
        return k1 * k2
    op = phi[0]
    if op == "not":
        return B0(False, k1, k2, phi[1]) if pol else B0(False, k2, k1, phi[1])
    if op == "and":
        if pol:
            return B0(True, B0(True, k1, k2, phi[1]), k2, phi[2])
        return B0(True, B0(True, k2, k1, phi[1]), k1, phi[2])
    if op == "or":
        if pol:
            return B0(True, k1, B0(True, k1, k2, phi[1]), phi[2])
        return B0(True, k2, B0(True, k2, k1, phi[1]), phi[2])
    raise ValueError(op)

# ---------------------------------------------------------------- the rule table
def is_atom(phi):
    return isinstance(phi, str)

def rule_of(env, node):
    """What the table says about a node under `env`:
       ("ax",) | ("atom",) | ("one", ns) | ("two", n1, n2)   — as ZCut.Ax/RuleC/Rule2."""
    s, phi = node
    if is_atom(phi):
        cell = env.get(phi, ALL) & s
        return ("ax",) if not cell else ("atom",)
    op = phi[0]
    if op == "imp":
        return ("one", [(s, ("or", ("not", phi[1]), phi[2]))])
    if op == "xor":
        return ("one", [(s, ("or", ("and", phi[1], ("not", phi[2])), ("and", ("not", phi[1]), phi[2])))])
    if op == "xnor":
        return ("one", [(s, ("or", ("and", phi[1], phi[2]), ("and", ("not", phi[1]), ("not", phi[2]))))])
    bT, bF = T in s, F in s
    if not bT and not bF:
        return ("ax",)
    if bT and bF:
        return ("one", [])
    if op == "not":
        return ("one", [(SF, phi[1])] if bT else [(SP, phi[1])])
    if op == "and":
        return ("one", [(ST, phi[1]), (ST, phi[2])]) if bT else ("two", [(SN, phi[1])], [(SN, phi[2])])
    if op == "or":
        return ("two", [(ST, phi[1])], [(ST, phi[2])]) if bT else ("one", [(SN, phi[1]), (SN, phi[2])])
    raise ValueError(op)

def narrow(env, node):
    s, a = node
    e2 = dict(env)
    e2[a] = env.get(a, ALL) & s
    return e2

# ---------------------------------------------------------------- trees
# ("ax", pos) | ("atom", pos, t) | ("one", pos, ns, t) | ("two", pos, n1, n2, t1, t2)

def leaves(t):
    k = t[0]
    if k == "ax":
        return 1
    if k == "atom":
        return leaves(t[2])
    if k == "one":
        return leaves(t[3])
    return leaves(t[4]) + leaves(t[5])

def build(env, S):
    """The engine: always the head. Returns a tree or None (open)."""
    if not S:
        return None
    node, rest = S[0], S[1:]
    r = rule_of(env, node)
    if r[0] == "ax":
        return ("ax", 0)
    if r[0] == "atom":
        t = build(narrow(env, node), rest)
        return None if t is None else ("atom", 0, t)
    if r[0] == "one":
        t = build(env, r[1] + rest)
        return None if t is None else ("one", 0, r[1], t)
    t1 = build(env, r[1] + rest)
    t2 = build(env, r[2] + rest)
    if t1 is None or t2 is None:
        return None
    return ("two", 0, r[1], r[2], t1, t2)

def check(env, S, t):
    """Re-verify a tree against the table. Raises on any defect."""
    k = t[0]
    pos = t[1]
    node = S[pos]
    rest = S[:pos] + S[pos + 1:]
    r = rule_of(env, node)
    if k == "ax":
        assert r[0] == "ax", ("not an axiom", node, env.get(node[1]))
        return
    if k == "atom":
        assert r[0] == "atom", ("atom rule on empty cell", node)
        check(narrow(env, node), rest, t[2])
        return
    if k == "one":
        assert r[0] == "one" and r[1] == t[2], ("wrong one-premise rule", node, r, t[2])
        check(env, t[2] + rest, t[3])
        return
    assert r[0] == "two" and r[1] == t[2] and r[2] == t[3], ("wrong two-premise rule", node)
    check(env, t[2] + rest, t[4])
    check(env, t[3] + rest, t[5])

# ---------------------------------------------------------------- structural operations
def shift_pos(p, q):
    """Position of an old element p once a node is inserted at index q."""
    return p if p < q else p + 1

def weak(t, q):
    """der_weak: insert a node at index q of the sequent (never used by the tree)."""
    k = t[0]
    p = t[1]
    p2 = shift_pos(p, q)
    q2 = q if q <= p else q - 1          # index of the inserted node in the remainder
    if k == "ax":
        return ("ax", p2)
    if k == "atom":
        return ("atom", p2, weak(t[2], q2))
    if k == "one":
        return ("one", p2, t[2], weak(t[3], len(t[2]) + q2))
    return ("two", p2, t[2], t[3], weak(t[4], len(t[2]) + q2), weak(t[5], len(t[3]) + q2))

def perm(t, order):
    """der_perm: new sequent = [old[i] for i in order]."""
    k = t[0]
    p = t[1]
    p2 = order.index(p)
    rest_order = [o if o < p else o - 1 for o in order if o != p]
    if k == "ax":
        return ("ax", p2)
    if k == "atom":
        return ("atom", p2, perm(t[2], rest_order))
    if k == "one":
        n = len(t[2])
        return ("one", p2, t[2], perm(t[3], list(range(n)) + [o + n for o in rest_order]))
    n1, n2 = len(t[2]), len(t[3])
    return ("two", p2, t[2], t[3],
            perm(t[4], list(range(n1)) + [o + n1 for o in rest_order]),
            perm(t[5], list(range(n2)) + [o + n2 for o in rest_order]))

def der_swap_front(t, a, b, n_total):
    order = list(range(a, a + b)) + list(range(a)) + list(range(a + b, n_total))
    return perm(t, order)

def pick_pick(p, px):
    """(same) or (index of x in Sy, index of y in S')."""
    if p == px:
        return None
    ix = px if px < p else px - 1     # x inside S minus y
    iy = p if p < px else p - 1       # y inside S minus x
    return ix, iy

# ---------------------------------------------------------------- inversions
def inv1(env, S, t, px, ns):
    """inv1: S with node at px admitting RuleC ns  ->  tree for ns ++ S'."""
    k, p = t[0], t[1]
    y = S[p]
    same = pick_pick(p, px)
    Sp = S[:px] + S[px + 1:]
    if k == "ax":
        assert same is not None, "axiom against a rule on the same node"
        ix, iy = same
        return ("ax", len(ns) + iy)
    if k == "atom":
        assert same is not None
        ix, iy = same
        Sy = S[:p] + S[p + 1:]
        return ("atom", len(ns) + iy, inv1(narrow(env, y), Sy, t[2], ix, ns))
    if k == "one":
        if same is None:
            assert t[2] == ns, ("determinism", t[2], ns)
            return t[3]
        ix, iy = same
        Sy = S[:p] + S[p + 1:]
        ns2 = t[2]
        t2 = inv1(env, ns2 + Sy, t[3], len(ns2) + ix, ns)   # ns ++ (ns2 ++ S3)
        S3 = Sy[:ix] + Sy[ix + 1:]
        t3 = der_swap_front(t2, len(ns), len(ns2), len(ns) + len(ns2) + len(S3))
        return ("one", len(ns) + iy, ns2, t3)
    assert same is not None, "two-premise rule against a one-premise rule on the same node"
    ix, iy = same
    Sy = S[:p] + S[p + 1:]
    n1, n2 = t[2], t[3]
    S3 = Sy[:ix] + Sy[ix + 1:]
    a = inv1(env, n1 + Sy, t[4], len(n1) + ix, ns)
    b = inv1(env, n2 + Sy, t[5], len(n2) + ix, ns)
    a = der_swap_front(a, len(ns), len(n1), len(ns) + len(n1) + len(S3))
    b = der_swap_front(b, len(ns), len(n2), len(ns) + len(n2) + len(S3))
    return ("two", len(ns) + iy, n1, n2, a, b)

def inv2(env, S, t, px, n1, n2):
    """inv2: node at px admitting Rule2 n1 n2  ->  (tree for n1 ++ S', tree for n2 ++ S')."""
    k, p = t[0], t[1]
    y = S[p]
    same = pick_pick(p, px)
    if k == "ax":
        assert same is not None
        ix, iy = same
        return ("ax", len(n1) + iy), ("ax", len(n2) + iy)
    if k == "atom":
        assert same is not None
        ix, iy = same
        Sy = S[:p] + S[p + 1:]
        a, b = inv2(narrow(env, y), Sy, t[2], ix, n1, n2)
        return ("atom", len(n1) + iy, a), ("atom", len(n2) + iy, b)
    if k == "one":
        assert same is not None
        ix, iy = same
        Sy = S[:p] + S[p + 1:]
        ns = t[2]
        S3 = Sy[:ix] + Sy[ix + 1:]
        a, b = inv2(env, ns + Sy, t[3], len(ns) + ix, n1, n2)
        a = der_swap_front(a, len(n1), len(ns), len(n1) + len(ns) + len(S3))
        b = der_swap_front(b, len(n2), len(ns), len(n2) + len(ns) + len(S3))
        return ("one", len(n1) + iy, ns, a), ("one", len(n2) + iy, ns, b)
    if same is None:
        assert (t[2], t[3]) == (n1, n2), "determinism"
        return t[4], t[5]
    ix, iy = same
    Sy = S[:p] + S[p + 1:]
    m1, m2 = t[2], t[3]
    S3 = Sy[:ix] + Sy[ix + 1:]
    a1, a2 = inv2(env, m1 + Sy, t[4], len(m1) + ix, n1, n2)
    b1, b2 = inv2(env, m2 + Sy, t[5], len(m2) + ix, n1, n2)
    a1 = der_swap_front(a1, len(n1), len(m1), len(n1) + len(m1) + len(S3))
    b1 = der_swap_front(b1, len(n1), len(m2), len(n1) + len(m2) + len(S3))
    a2 = der_swap_front(a2, len(n2), len(m1), len(n2) + len(m1) + len(S3))
    b2 = der_swap_front(b2, len(n2), len(m2), len(n2) + len(m2) + len(S3))
    return (("two", len(n1) + iy, m1, m2, a1, b1), ("two", len(n2) + iy, m1, m2, a2, b2))

def inv_atom(env, S, t, px):
    """inv_atom: node (s, atom) at px. Returns None (cell dies) or a tree for S'
    under the narrowed env."""
    k, p = t[0], t[1]
    x = S[px]
    y = S[p]
    same = pick_pick(p, px)
    cell = env.get(x[1], ALL) & x[0]
    if k == "ax":
        if same is None:
            return None
        ix, iy = same
        if not cell:
            return None
        return ("ax", iy)                      # y stays an axiom under the narrowed env
    if k == "atom":
        if same is None:
            return t[2]
        ix, iy = same
        Sy = S[:p] + S[p + 1:]
        if not cell:
            return None
        sub = inv_atom(narrow(env, y), Sy, t[2], ix)
        # under env[x], y is an atom node: axiom if its cell dies there, else continue
        env_x = narrow(env, x)
        if sub is None:
            return ("ax", iy)                  # (x narrowed) ∩ y's sign is empty
        return ("atom", iy, sub)
    if k == "one":
        assert same is not None
        ix, iy = same
        Sy = S[:p] + S[p + 1:]
        ns = t[2]
        sub = inv_atom(env, ns + Sy, t[3], len(ns) + ix)
        if sub is None:
            return None
        return ("one", iy, ns, sub)
    assert same is not None
    ix, iy = same
    Sy = S[:p] + S[p + 1:]
    n1, n2 = t[2], t[3]
    a = inv_atom(env, n1 + Sy, t[4], len(n1) + ix)
    if a is None:
        return None
    b = inv_atom(env, n2 + Sy, t[5], len(n2) + ix)
    if b is None:
        return None
    return ("two", iy, n1, n2, a, b)

# ---------------------------------------------------------------- the cuts
def cut_env(env0, n, a, b, S, t1, t2):
    """cut_env: t1 under env0[n∩a], t2 under env0[n∩b], a∪b ⊇ cell  ->  tree under env0."""
    env_a = dict(env0); env_a[n] = env0.get(n, ALL) & a
    env_b = dict(env0); env_b[n] = env0.get(n, ALL) & b
    k, p = t1[0], t1[1]
    y = S[p]
    Sy = S[:p] + S[p + 1:]
    if k == "ax":
        if is_atom(y[1]) and y[1] == n:
            # e0 n ∩ a ∩ s' is empty
            r = inv_atom(env_b, S, t2, p)
            if r is None:
                return ("ax", p)               # both halves empty: cell ∩ s' empty
            return ("atom", p, r)              # cell ∩ s' ⊆ b: continue with t2's continuation
        return ("ax", p)
    if k == "atom":
        r = inv_atom(env_b, S, t2, p)
        if r is None:
            # other cell: e0 m ∩ s' is empty -> axiom;
            # same cell: e0 n ∩ b ∩ s' empty, so e0 n ∩ s' ⊆ a and t1's continuation stands as is
            return ("ax", p) if y[1] != n else ("atom", p, t1[2])
        env0y = narrow(env0, y)
        return ("atom", p, cut_env(env0y, n, a, b, Sy, t1[2], r))
    if k == "one":
        ns = t1[2]
        r = inv1(env_b, S, t2, p, ns)
        return ("one", p, ns, cut_env(env0, n, a, b, ns + Sy, t1[3], r))
    n1, n2 = t1[2], t1[3]
    r1, r2 = inv2(env_b, S, t2, p, n1, n2)
    return ("two", p, n1, n2, cut_env(env0, n, a, b, n1 + Sy, t1[4], r1),
            cut_env(env0, n, a, b, n2 + Sy, t1[5], r2))

SIG1 = {True: ST, False: SF}
SIG2 = {True: SN, False: SP}

def cutP(env, pol, phi, S, t1, t2):
    """cutP: t1 for (sig1 pol, φ)::S, t2 for (sig2 pol, φ)::S  ->  tree for S."""
    s1, s2 = SIG1[pol], SIG2[pol]
    if is_atom(phi):
        r1 = inv_atom(env, [(s1, phi)] + S, t1, 0)
        r2 = inv_atom(env, [(s2, phi)] + S, t2, 0)
        if r1 is None and r2 is None:
            raise AssertionError("cell empty on both sides")
        if r1 is None:
            return r2                          # cell ⊆ s2: narrowing by s2 changes nothing
        if r2 is None:
            return r1
        return cut_env(env, phi, s1, s2, S, r1, r2)
    op = phi[0]
    if op in ("imp", "xor", "xnor"):
        rw = rule_of(env, (s1, phi))[1]
        a = inv1(env, [(s1, phi)] + S, t1, 0, rw)
        b = inv1(env, [(s2, phi)] + S, t2, 0, rule_of(env, (s2, phi))[1])
        return cutP(env, pol, rw[0][1], S, a, b)
    if op == "not":
        psi = phi[1]
        if pol:
            a = inv1(env, [(s1, phi)] + S, t1, 0, [(SF, psi)])
            b = inv1(env, [(s2, phi)] + S, t2, 0, [(SP, psi)])
            return cutP(env, False, psi, S, a, b)
        a = inv1(env, [(s1, phi)] + S, t1, 0, [(SP, psi)])   # F:¬ψ -> P:ψ
        b = inv1(env, [(s2, phi)] + S, t2, 0, [(SF, psi)])   # P:¬ψ -> F:ψ
        return cutP(env, False, psi, S, b, a)
    psi, chi = phi[1], phi[2]
    if op == "and":
        if pol:
            a = inv1(env, [(s1, phi)] + S, t1, 0, [(ST, psi), (ST, chi)])
            b1, b2 = inv2(env, [(s2, phi)] + S, t2, 0, [(SN, psi)], [(SN, chi)])
            c = cutP(env, True, psi, [(ST, chi)] + S, a, weak(b1, 1))
            return cutP(env, True, chi, S, c, b2)
        a1, a2 = inv2(env, [(s1, phi)] + S, t1, 0, [(SN, psi)], [(SN, chi)])
        b = inv1(env, [(s2, phi)] + S, t2, 0, [(ST, psi), (ST, chi)])
        c = cutP(env, True, psi, [(ST, chi)] + S, b, weak(a1, 1))
        return cutP(env, True, chi, S, c, a2)
    if op == "or":
        if pol:
            a1, a2 = inv2(env, [(s1, phi)] + S, t1, 0, [(ST, psi)], [(ST, chi)])
            b = inv1(env, [(s2, phi)] + S, t2, 0, [(SN, psi), (SN, chi)])
            c = cutP(env, True, psi, [(SN, chi)] + S, weak(a1, 1), b)
            return cutP(env, True, chi, S, a2, c)
        a = inv1(env, [(s1, phi)] + S, t1, 0, [(SN, psi), (SN, chi)])
        b1, b2 = inv2(env, [(s2, phi)] + S, t2, 0, [(ST, psi)], [(ST, chi)])
        c = cutP(env, True, psi, [(SN, chi)] + S, weak(b1, 1), a)
        return cutP(env, True, chi, S, b2, c)
    raise ValueError(op)

def _neg(f, d):
    for _ in range(d):
        f = ("not", f)
    return f

# ---------------------------------------------------------------- the measurement
def main():
    print("=" * 72)
    print("E55. SYNTACTIC CUT ELIMINATION: THE PROCEDURE, RUN, AND ITS BOUND MEASURED")
    print("=" * 72)
    forms = pool_formulas()
    seqs = pool_sequents(forms)
    env0 = {}
    fired = 0
    viol_bound = 0
    equal_bound = 0
    max_ratio_kB = 0.0
    max_ratio_kk0 = 0.0
    worst_kk0 = None
    shortened = 0
    checked_trees = 0
    max_k = 0
    for S in seqs:
        for phi in forms:
            t1 = build(env0, [(ST, phi)] + S)
            t2 = build(env0, [(SN, phi)] + S)
            if t1 is None or t2 is None:
                continue
            fired += 1
            k1, k2 = leaves(t1), leaves(t2)
            t = cutP(env0, True, phi, S, t1, t2)
            check(env0, S, t)                      # the oracle: every tree re-verified
            checked_trees += 1
            k = leaves(t)
            B = B0(True, k1, k2, basis(phi))
            t0 = build(env0, S)
            assert t0 is not None, "cut-free closure lost (admissibility violated)"
            k0 = leaves(t0)
            max_k = max(max_k, k)
            if k > B:
                viol_bound += 1
                print(f"  ✗ BOUND VIOLATED S={S} φ={phi}: k={k} B={B}")
            if k == B:
                equal_bound += 1
            max_ratio_kB = max(max_ratio_kB, k / B)
            if k / k0 > max_ratio_kk0:
                max_ratio_kk0 = k / k0
                worst_kk0 = (S, phi, k, k0, k1, k2, B)
            if k0 > k1 + k2:
                shortened += 1
    print(f"\n  pool: {len(forms)} formulas, {len(seqs)} sequents; cut instances with both"
          f" premises closed: {fired}")
    print(f"  trees built by the procedure and re-verified against the rules: {checked_trees}")
    print(f"\n  (1) bound: violations {viol_bound} of {fired}"
          f" ({'✓ k ≤ B on every instance' if viol_bound == 0 else '✗'})")
    print(f"  (2) tightness: k = B on {equal_bound} of {fired}; max k/B = {max_ratio_kB:.3f};"
          f" largest cut-free tree produced: {max_k} leaves")
    print(f"  (3) price against plain search: max k/k₀ = {max_ratio_kk0:.2f}")
    if worst_kk0:
        S, phi, k, k0, k1, k2, B = worst_kk0
        print(f"      worst: S={S} φ={phi}: procedure {k} leaves, engine {k0}, premises {k1}+{k2}, B={B}")
    print(f"      instances where the cut SHORTENS (k₀ > k₁+k₂): {shortened} of {fired}"
          f" — {'cut buys nothing on this pool' if shortened == 0 else 'cut pays here'}")
    # the T/F pair: refused on an atom, granted on compounds — as in Lean
    print("\n### The classical pair T/F")
    S = [(SN, "p"), (SP, "p")]
    tT = build(env0, [(ST, "p")] + S); tF = build(env0, [(SF, "p")] + S); t_atom = build(env0, S)
    print(f"  atom p, S = {{N:p, P:p}}: T-premise {'closes' if tT else 'open'},"
          f" F-premise {'closes' if tF else 'open'}, S itself {'closes' if t_atom else 'OPEN — Z escapes'}")
    viol_tf = fired_tf = 0
    for Sq in seqs:
        for phi in forms:
            if is_atom(phi):
                continue
            if build(env0, [(ST, phi)] + Sq) and build(env0, [(SF, phi)] + Sq):
                fired_tf += 1
                if build(env0, Sq) is None:
                    viol_tf += 1
    print(f"  compounds: T/F cut instances {fired_tf}, violations {viol_tf}"
          f" ({'✓ admissible on compounds' if viol_tf == 0 else '✗'})")
    # ---- the bound's own growth, computed (k₁ = k₂ = 2): the shape of the recursion
    print("\n### The bound B0, computed on chains (k₁ = k₂ = 2)")
    def chain(op, d):
        f = "p0"
        for i in range(1, d + 1):
            f = (op, f, f"p{i}")
        return f
    for op in ("or", "and"):
        row = [B0(True, 2, 2, chain(op, d)) for d in range(0, 7)]
        print(f"  {op:3} chain, depth 0..6: {row}   — ×2 per level")
    row = [B0(True, 2, 3, _neg("p", d)) for d in range(0, 5)]
    print(f"  ¬-chain over p, k₁=2 k₂=3, depth 0..4: {row}   — ¬ costs nothing, only flips the pair")

    # ---- a deeper pool: random formulas, to see the procedure move away from the engine
    import random
    rnd = random.Random(55)
    atoms = ["p", "q", "r"]
    def rand_formula(depth):
        if depth == 0 or rnd.random() < 0.25:
            return rnd.choice(atoms)
        op = rnd.choice(["not", "and", "or", "imp", "xor"])
        if op == "not":
            return ("not", rand_formula(depth - 1))
        return (op, rand_formula(depth - 1), rand_formula(depth - 1))
    deep_fired = deep_viol = deep_eq = 0
    max_kB2 = 0.0; max_kk0_2 = 0.0; worst2 = None; short2 = 0; max_k2 = 0; max_B2 = 0
    tries = 0; skipped_big = 0; CAP = 1000000
    below = equal = above = 0; sum_ratio = 0.0; max_B_run = 0
    while deep_fired < 300 and tries < 20000:
        tries += 1
        phi = rand_formula(3)
        Sq = [(rnd.choice([ST, SF, SP, SN]), rand_formula(2)) for _ in range(rnd.choice([1, 2]))]
        t1 = build(env0, [(ST, phi)] + Sq); t2 = build(env0, [(SN, phi)] + Sq)
        if t1 is None or t2 is None:
            continue
        k1, k2 = leaves(t1), leaves(t2)
        if B0(True, k1, k2, basis(phi)) > CAP:
            skipped_big += 1                   # the output tree itself would not fit: the blow-up, met
            continue
        deep_fired += 1
        t = cutP(env0, True, phi, Sq, t1, t2)
        check(env0, Sq, t)
        k = leaves(t); B = B0(True, k1, k2, basis(phi))
        t0 = build(env0, Sq); assert t0 is not None
        k0 = leaves(t0)
        max_k2 = max(max_k2, k); max_B2 = max(max_B2, B)
        if k < k0: below += 1
        elif k == k0: equal += 1
        else: above += 1
        sum_ratio += k / k0
        if k > B: deep_viol += 1
        if k == B: deep_eq += 1
        max_kB2 = max(max_kB2, k / B)
        if k / k0 > max_kk0_2:
            max_kk0_2 = k / k0; worst2 = (Sq, phi, k, k0, k1, k2, B)
        if k0 > k1 + k2: short2 += 1
    print(f"\n### A deeper pool: {deep_fired} random cut instances (formulas to depth 3 over 3 atoms, seed 55)")
    print(f"  instances whose PROVED bound exceeded {CAP} leaves and were not run: {skipped_big}"
          f" — the blow-up is real, not a story")
    print(f"  trees re-verified: {deep_fired}; bound violations: {deep_viol}"
          f" ({'✓' if deep_viol == 0 else '✗'}); k = B on {deep_eq}; max k/B = {max_kB2:.3f}")
    print(f"  largest tree produced: {max_k2} leaves; largest bound: {max_B2}")
    print(f"  max k/k₀ (procedure against plain search): {max_kk0_2:.2f}")
    if worst2:
        Sq, phi, k, k0, k1, k2, B = worst2
        print(f"      worst: φ={phi}\n             S={Sq}\n             procedure {k}, engine {k0}, premises {k1}+{k2}, B={B}")
    print(f"  instances where the cut SHORTENS (k₀ > k₁+k₂): {short2} of {deep_fired}")
    print(f"  procedure output against the engine's direct derivation: below {below}, equal {equal},"
          f" above {above}; mean k/k₀ = {sum_ratio / max(1, deep_fired):.3f}")
    print(f"  NOTE: selection — instances with B > {CAP} were skipped; they are the deep/wide ones,"
          f" so 'never above' is a statement about the {deep_fired} that ran, not about all cuts")
    ok = viol_bound == 0 and viol_tf == 0 and t_atom is None and deep_viol == 0
    print("\n" + ("E55 GREEN: the procedure runs, every tree it builds re-verifies, and the"
                  " proved bound holds on the pool" if ok else "E55 RED"))
    return 0 if ok else 1

if __name__ == "__main__":
    import sys
    sys.exit(main())
