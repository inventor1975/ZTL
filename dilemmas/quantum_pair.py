# -*- coding: utf-8 -*-
"""quantum_pair — TWO quanta: which law of logic falls on the pair.

The curator's question (2026-07-19): "куда пропадает момент при изменении
спина — какой закон логики отваливается на системе из двух квантов?"
Measured here on the SINGLET — the pair with total spin 0 — over the full
projection lattice of C^4 (pure stdlib linear algebra, no numpy).

  1. THE PAIR IS GROUNDED, THE PARTS ARE ALL FOG. Pair propositions are
     TRUE: "spins are opposite" = T, "total spin = 0" = T. Yet EVERY
     local proposition — "spin of particle 1 is up" — is Z(0.50) along
     EVERY axis (Z, X, Y), for both particles. The whole is fully
     grounded; no part carries an address for the value.

  2. WHAT FALLS ON TWO QUANTA: TRUTH-FUNCTIONALITY — the cover law
     or(a,b)=T ⟺ a=T or b=T, which the ZTL core keeps as a THEOREM for
     its own tables (cover_or_T, ZTL.lean, empty axiom list). Here:
     OPP = join(|ud>, |du>) is TRUE while BOTH disjuncts are Z — a true
     disjunction with no true disjunct, built from parts that are all
     unverified. On ONE quantum this law fell in its LEM form
     (x ∨ x^⊥ = ⊤, neither side true); on TWO it falls in CORRELATION
     form — and the correlation form IS entanglement written as a
     logical fact: the truth is stored in the pair and not distributed
     to the parts.

  3. WHERE DOES THE MOMENTUM GO: NOWHERE. "Total spin = 0" is a TRUE
     proposition of the pair; the "disappearance" is what happens when
     the pair's question is projected into the parts' logic, where all
     addresses are empty (Z on every axis). Conservation is a property
     of the whole; the parts do not carry half each.

  4. THE CORRECTED HYPOTHESIS (honesty section — the first guess was
     WRONG and the measurement caught it). Expected: the singlet is NOT
     expressible from local propositions by lattice operations (failure
     of lattice compositionality). Measured: it IS — the bounded closure
     of the local propositions under meet/join reaches the singlet line
     (meet of two product-spanned planes; see MEASURED). Quantum ∧/∨
     are strong enough to BUILD the pair's propositions from local
     material — what is NOT compositional is the TRUTH VALUE, not the
     lattice. The law that falls is semantic (truth-functionality),
     not syntactic (expressibility).

  5. THE CURATOR EXPECTED ¬¬ TO FALL — IT DOES NOT, and that is the
     PSSL mirror in the flesh: the orthocomplement is involutive,
     ¬¬P = P holds on every subspace of the pair lattice (measured
     here; cf. dne_holds on MO2, QuantumWitness.lean, empty axiom
     list). Quantum keeps the double negation iron and drops the
     disjunctive side (LEM-cover / truth-functionality); ZTL keeps the
     cover law as a theorem and drops ¬¬p → p (until-verification).
     Mirror sacrifices, extended from one quantum to the pair.

MEASURED (this file, deterministic, pure stdlib):
  §1 pair: OPP=T, total-0=T; locals: 8 propositions (2 particles ×
     4 axes incl. Y) — ALL Z(0.50).
  §2 cover: join(P_ud, P_du)=T with both disjuncts Z(0.50).
  §4 closure from 8 local generators (Z,X bases, both particles):
     round 1: 42 subspaces; round 2: 114 (OPP reached); round 3: 258,
     SINGLET REACHED — via meet of two product-spanned planes
     (span{|ud>,|du>} ∩ span{|+->,|-+>}, witness verified) — lattice
     compositionality HOLDS; the initial guess is refuted and kept
     here as the record.
  §5 involution ¬¬P=P: exact on every subspace in the closure (258/258).

Honest scope: this is textbook two-qubit structure (EPR/Bell territory);
nothing new about quantum mechanics. The point is the LOGICAL ledger:
which law survives the pair and which falls — and the honest note that
the quantum Z here is ONTIC vacancy (by Bell, local values cannot even
be consistently assigned), not ZTL's epistemic flag: the Z↔superposition
kinship stays a rhyme, and the pair shows exactly where the rhyme ends.
"""
import math

EPS = 1e-9


# ------------------------------------------------- C^4, pure stdlib
def dot(u, v):
    return sum(a.conjugate() * b for a, b in zip(u, v))


def norm(u):
    return math.sqrt(abs(dot(u, u)))


def scale(u, c):
    return tuple(c * a for a in u)


def sub(u, v):
    return tuple(a - b for a, b in zip(u, v))


def gram_schmidt(vectors):
    """Orthonormal basis of the span."""
    basis = []
    for v in vectors:
        w = v
        for b in basis:
            w = sub(w, scale(b, dot(b, w)))
        n = norm(w)
        if n > 1e-7:
            basis.append(scale(w, 1 / n))
    return basis


E = [tuple(1 + 0j if i == k else 0j for i in range(4)) for k in range(4)]


def ortho(S):
    """Orthocomplement: quantum negation of the subspace."""
    basis = list(S)
    out = []
    for e in E:
        w = e
        for b in basis + out:
            w = sub(w, scale(b, dot(b, w)))
        n = norm(w)
        if n > 1e-7:
            out.append(scale(w, 1 / n))
    return out


def join(A, B):
    return gram_schmidt(list(A) + list(B))


def meet(A, B):
    return ortho(join(ortho(A), ortho(B)))


def proj_matrix(S):
    return tuple(tuple(sum(b[i] * b[j].conjugate() for b in S)
                       for j in range(4)) for i in range(4))


def skey(S):
    M = proj_matrix(S)
    return tuple((round(z.real, 5) + 0.0, round(z.imag, 5) + 0.0)
                 for row in M for z in row)


def status(S, psi):
    """T / F / Z(p) of the proposition 'state lies in S' at state psi."""
    p = sum(abs(dot(b, psi)) ** 2 for b in S)
    if p > 1 - EPS:
        return "T"
    if p < EPS:
        return "F"
    return f"Z({p:.2f})"


def sspan(*vecs):
    return gram_schmidt([tuple(complex(x) for x in v) for v in vecs])


# ------------------------------------------------- states and props
R2 = 1 / math.sqrt(2)
SINGLET = (0j, R2 + 0j, -R2 + 0j, 0j)          # (|ud> - |du>)/√2

# one-qubit propositions (as 2-vectors), then lifted to a particle
UP, DOWN = (1, 0), (0, 1)
PLUS, MINUS = (R2, R2), (R2, -R2)
YP, YM = (R2, R2 * 1j), (R2, -R2 * 1j)


def lift1(v):
    """particle 1 has 1-qubit property v (span of v⊗e for e basis)."""
    return sspan((v[0], 0, v[1], 0), (0, v[0], 0, v[1]))


def lift2(v):
    return sspan((v[0], v[1], 0, 0), (0, 0, v[0], v[1]))


if __name__ == "__main__":
    print("=" * 72)
    print("QUANTUM PAIR: which law of logic falls on TWO quanta (the singlet)")
    print("=" * 72)

    # ---- 1. the pair grounded, the parts all fog -----------------------
    P_ud, P_du = sspan(E[1]), sspan(E[2])
    OPP = sspan(E[1], E[2])
    TOTAL0 = sspan(SINGLET)
    print("\n### 1. Pair propositions vs part propositions")
    print(f"  'spins are opposite' (pair): {status(OPP, SINGLET)}")
    print(f"  'total spin = 0'    (pair): {status(TOTAL0, SINGLET)}")
    locals_all = [("spin1=up  (Z axis)", lift1(UP)),
                  ("spin1=+x  (X axis)", lift1(PLUS)),
                  ("spin1=+y  (Y axis)", lift1(YP)),
                  ("spin1=down       ", lift1(DOWN)),
                  ("spin2=up  (Z axis)", lift2(UP)),
                  ("spin2=+x  (X axis)", lift2(PLUS)),
                  ("spin2=+y  (Y axis)", lift2(YP)),
                  ("spin2=down       ", lift2(DOWN))]
    all_z = True
    for name, S in locals_all:
        st = status(S, SINGLET)
        all_z &= st.startswith("Z")
        print(f"  {name}: {st}")
    assert all_z
    print("  → the whole is fully grounded; EVERY local address is empty.")

    # ---- 2. the cover law falls in correlation form --------------------
    print("\n### 2. Truth-functionality falls: a true OR with no true disjunct")
    J = join(P_ud, P_du)
    print(f"  join(|ud>, |du>) at the singlet: {status(J, SINGLET)}")
    print(f"  disjunct |ud>: {status(P_ud, SINGLET)};  "
          f"disjunct |du>: {status(P_du, SINGLET)}")
    assert status(J, SINGLET) == "T"
    assert status(P_ud, SINGLET).startswith("Z")
    print("  → ZTL keeps this as a THEOREM for its tables (cover_or_T);")
    print("    one quantum broke it in LEM form (x∨x⊥=⊤); the pair breaks")
    print("    it in CORRELATION form — entanglement as a logical fact.")

    # ---- 3. where the momentum goes ------------------------------------
    print("\n### 3. Where does the momentum go? NOWHERE.")
    print(f"  'total spin = 0' is {status(TOTAL0, SINGLET)} — a true, "
          f"conserved pair-proposition;")
    print("  the 'disappearance' is the projection of the pair's question")
    print("  into the parts' logic, where all addresses are Z. The whole")
    print("  carries the truth; the parts do not carry half each.")

    # ---- 4. the corrected hypothesis: lattice compositionality HOLDS ---
    print("\n### 4. The corrected hypothesis (the measurement caught me)")
    print("  Guessed: the singlet is NOT lattice-expressible from local")
    print("  propositions. Measured: it IS — the closure reaches it:")
    gens = [lift1(v) for v in (UP, DOWN, PLUS, MINUS)] + \
           [lift2(v) for v in (UP, DOWN, PLUS, MINUS)]
    closure = {skey(S): S for S in gens}
    closure[skey([])] = []
    closure[skey(E)] = gram_schmidt(E)
    singlet_hit = opp_hit = None
    for rnd in (1, 2, 3):
        items = list(closure.values())
        new = {}
        for i in range(len(items)):
            for j in range(i + 1, len(items)):
                for R in (join(items[i], items[j]), meet(items[i], items[j])):
                    k = skey(R)
                    if k not in closure and k not in new:
                        new[k] = R
        closure.update(new)
        if opp_hit is None and skey(OPP) in closure:
            opp_hit = rnd
        if singlet_hit is None and skey(TOTAL0) in closure:
            singlet_hit = rnd
        print(f"    round {rnd}: {len(closure)} subspaces"
              + (f"; OPP reached (round {opp_hit})" if opp_hit == rnd else "")
              + (f"; SINGLET REACHED (round {singlet_hit})"
                 if singlet_hit == rnd else ""))
    assert singlet_hit is not None
    W = meet(sspan(E[1], E[2]),
             sspan((0.5, -0.5, 0.5, -0.5), (0.5, 0.5, -0.5, -0.5)))
    print(f"    the witness: span(ud,du) ∩ span(+-,-+) = "
          f"{'the singlet line' if skey(W) == skey(TOTAL0) else '?'}")
    print("  → quantum ∧/∨ BUILD the pair's propositions from local")
    print("    material; what is not compositional is the TRUTH VALUE.")
    print("    The falling law is semantic, not syntactic.")

    # ---- 5. what the curator expected: ¬¬ — and it holds ---------------
    print("\n### 5. ¬¬ does NOT fall — the PSSL mirror in the flesh")
    bad = sum(1 for S in closure.values() if skey(ortho(ortho(S))) != skey(S))
    print(f"  involution ¬¬P = P checked on the whole closure: "
          f"{len(closure) - bad}/{len(closure)} exact, violations {bad}")
    assert bad == 0
    print("  → quantum keeps double negation IRON (cf. dne_holds, MO2,")
    print("    empty axiom list) and drops the disjunctive side; ZTL keeps")
    print("    the cover law as a theorem and drops ¬¬p→p. Mirror")
    print("    sacrifices — now extended from one quantum to the pair.")

    print("\n  ✓ pair grounded, parts all-Z; truth-functionality falls in")
    print("    correlation form; the momentum lives in the whole; the")
    print("    lattice composes, the truth does not; ¬¬ stands.")
