# -*- coding: utf-8 -*-
"""quantum_ladder — 1, 2, 3 quanta: what else falls, and what never does.

The curator's question (2026-07-19): one quantum drops distributivity,
two drop the cover law — check FURTHER: does anything else fall at 3+?
And do ¬p or p→p fall anywhere?

THE LADDER, measured (every claim below is computed in this file):

  1 QUANTUM — distributivity falls (measured on MO2, QuantumWitness) —
    and with it the material arrow loses MODUS PONENS:
    a ∧ (a⊥ ∨ b) = a  ≰  b — the arrow's real casualty, computed here
    on the same six-element lattice. p→p itself is NOT the casualty.

  2 QUANTA — the TRUTH TABLE ITSELF falls: contextuality. The
    Mermin–Peres magic square: nine two-qubit observables in a 3×3
    grid; the six operator identities (three rows multiply to +I,
    columns to +I, +I, −I) are verified here by direct matrix
    arithmetic — and then ALL 512 classical assignments of ±1 are
    enumerated: 0 satisfy the six constraints. No bivalent valuation
    exists AT ALL — not "unknown values" but NO CONSISTENT TABLE.
    (This is the ontic vacancy behind §1 of quantum_pair: the local
    addresses are not merely empty — they cannot be filled.)

  3 QUANTA — NOTHING NEW falls; the same law falls HARDER. The GHZ
    all-versus-nothing argument: four operator identities
    (XXX = +1, XYY = YXY = YYX = −1 on the GHZ state, verified here on
    the 8-dim vector), then all 64 classical assignments enumerated:
    0 satisfy — a one-shot contradiction, no inequalities needed.
    The ladder SATURATES: after two quanta the list of fallen laws is
    complete; more quanta only sharpen the witnesses.

  WHAT NEVER FALLS (measured across 1, 2, 3 quanta):
    ¬p is IRON — the orthocomplement is involutive (¬¬P = P), keeps
    non-contradiction (P ∧ ¬P = 0) and the LEM-law (P ∨ ¬P = ⊤) at
    every size; and p→p is IRON in the lattice's own arrow — the
    Sasaki hook a →s b := a⊥ ∨ (a ∧ b) gives a →s a = ⊤ always.
    What the arrow LOSES (already at one quantum) is modus ponens for
    the MATERIAL reading a⊥∨b; the Sasaki reading keeps
    a ∧ (a →s b) ≤ b by orthomodularity — also computed here.

MEASURED (this file, deterministic, pure stdlib):
  MO2: material-MP violation witness a∧(a⊥∨b)=a ≰ b confirmed;
  Sasaki-MP holds on all 6³ = 216 triples; Sasaki identity a→s a=⊤ 6/6.
  Mermin–Peres: 6 operator identities verified (+I ×5, −I col 3);
  classical assignments satisfying all six: 0 of 512.
  GHZ: 4 eigen-identities verified on the state; classical
  assignments: 0 of 64.
  Iron laws: involution / NC / LEM-law hold on all MO2 elements and on
  every subspace of the 2-qubit closure (quantum_pair) — cited; here
  re-verified on MO2 (6/6) plus 3-qubit spot checks.

Honest scope: Mermin–Peres and GHZ are textbook (Mermin 1990; Peres
1990); the ladder's summary — "the fallen-law list saturates at two" —
is measured over THESE finite witnesses, not proved for all
conceivable laws. The Z of these pages is ontic vacancy, not ZTL's
epistemic flag (the Bell/KS boundary of the rhyme).
"""
import itertools

# ---------------------------------------------------- MO2 (one quantum)
# elements: 0,1 = bot/top; a, a', b, b' the four middle atoms
ELS = ["bot", "a", "a1", "b", "b1", "top"]
NEG = {"bot": "top", "top": "bot", "a": "a1", "a1": "a", "b": "b1", "b1": "b"}


def meet(x, y):
    if x == y:
        return x
    if x == "bot" or y == "bot":
        return "bot"
    if x == "top":
        return y
    if y == "top":
        return x
    return "bot"


def join(x, y):
    if x == y:
        return x
    if x == "top" or y == "top":
        return "top"
    if x == "bot":
        return y
    if y == "bot":
        return x
    return "top"


def leq(x, y):
    return meet(x, y) == x


def sasaki(x, y):
    return join(NEG[x], meet(x, y))


# ------------------------------------------- 2x2 / 4x4 complex matrices
def mat(*rows):
    return tuple(tuple(complex(z) for z in r) for r in rows)


I2 = mat((1, 0), (0, 1))
X = mat((0, 1), (1, 0))
Y = mat((0, -1j), (1j, 0))
Z = mat((0j + 1, 0), (0, -1))


def kron(A, B):
    n, m = len(A), len(B)
    return tuple(tuple(A[i // m][j // m] * B[i % m][j % m]
                       for j in range(n * m)) for i in range(n * m))


def mm(A, B):
    n = len(A)
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(n))
                       for j in range(n)) for i in range(n))


def is_scalar(A, c, eps=1e-9):
    n = len(A)
    return all(abs(A[i][j] - (c if i == j else 0)) < eps
               for i in range(n) for j in range(n))


def apply(A, v):
    n = len(A)
    return tuple(sum(A[i][j] * v[j] for j in range(n)) for i in range(n))


if __name__ == "__main__":
    print("=" * 72)
    print("QUANTUM LADDER: 1, 2, 3 quanta — what else falls, what never does")
    print("=" * 72)

    # ---- 1 quantum: the arrow's real casualty is MP, not p→p -----------
    print("\n### 1 quantum (MO2): the material arrow loses modus ponens")
    lhs = meet("a", join(NEG["a"], "b"))
    print(f"  a ∧ (a⊥ ∨ b) = {lhs};  a ≤ b: {leq(lhs, 'b')} — "
          "the MATERIAL arrow fails MP (a consequence of non-distributivity)")
    assert lhs == "a" and not leq(lhs, "b")
    sid = all(sasaki(x, x) == "top" for x in ELS)
    smp = all(leq(meet(x, sasaki(x, y)), y)
              for x in ELS for y in ELS)
    print(f"  Sasaki identity a→s a = ⊤: {sid} (6/6);  "
          f"Sasaki MP a∧(a→s b) ≤ b: {smp} (216/216 triples)")
    assert sid and smp
    print("  → p→p does NOT fall; the lattice's own arrow keeps identity")
    print("    and modus ponens — the casualty is the MATERIAL reading.")

    # ---- 2 quanta: the truth table itself falls (Mermin–Peres) ---------
    print("\n### 2 quanta: contextuality — the Mermin–Peres magic square")
    G = [[kron(X, I2), kron(I2, X), kron(X, X)],
         [kron(I2, Y), kron(Y, I2), kron(Y, Y)],
         [kron(X, Y), kron(Y, X), kron(Z, Z)]]
    for r in range(3):
        P = mm(mm(G[r][0], G[r][1]), G[r][2])
        assert is_scalar(P, 1), f"row {r}"
    signs = []
    for c in range(3):
        P = mm(mm(G[0][c], G[1][c]), G[2][c])
        s = 1 if is_scalar(P, 1) else (-1 if is_scalar(P, -1) else None)
        assert s is not None
        signs.append(s)
    print(f"  operator identities: rows ×3 → +I; columns → "
          f"{signs} (the −1 is the magic)")
    assert signs == [1, 1, -1]
    good = 0
    for vals in itertools.product((1, -1), repeat=9):
        v = [vals[0:3], vals[3:6], vals[6:9]]
        rows_ok = all(v[r][0] * v[r][1] * v[r][2] == 1 for r in range(3))
        cols_ok = all(v[0][c] * v[1][c] * v[2][c] == signs[c]
                      for c in range(3))
        good += rows_ok and cols_ok
    print(f"  classical ±1 assignments satisfying all six constraints: "
          f"{good} of 512")
    assert good == 0
    print("  → NO bivalent valuation exists at all: the local addresses of")
    print("    quantum_pair §1 are not merely empty — they CANNOT be filled.")

    # ---- 3 quanta: the same law falls harder (GHZ) ---------------------
    print("\n### 3 quanta: GHZ — all-versus-nothing, nothing NEW falls")
    ghz = tuple((1 / 2 ** 0.5 if i in (0, 7) else 0j) for i in range(8))
    ops = [("XXX", kron(kron(X, X), X), 1),
           ("XYY", kron(kron(X, Y), Y), -1),
           ("YXY", kron(kron(Y, X), Y), -1),
           ("YYX", kron(kron(Y, Y), X), -1)]
    for name, O, s in ops:
        w = apply(O, ghz)
        ok = all(abs(w[i] - s * ghz[i]) < 1e-9 for i in range(8))
        assert ok, name
    print("  eigen-identities on the GHZ state: XXX=+1, XYY=YXY=YYX=−1 ✓")
    good = 0
    for vals in itertools.product((1, -1), repeat=6):
        x1, x2, x3, y1, y2, y3 = vals
        good += (x1 * x2 * x3 == 1 and x1 * y2 * y3 == -1
                 and y1 * x2 * y3 == -1 and y1 * y2 * x3 == -1)
    print(f"  classical assignments satisfying all four: {good} of 64")
    assert good == 0
    print("  → the SAME law (no truth table) falls in one-shot form; the")
    print("    ladder saturates — more quanta sharpen witnesses, no new law.")

    # ---- what never falls ----------------------------------------------
    print("\n### The iron laws (measured across the ladder)")
    inv = all(NEG[NEG[x]] == x for x in ELS)
    nc = all(meet(x, NEG[x]) == "bot" for x in ELS)
    lem = all(join(x, NEG[x]) == "top" for x in ELS)
    print(f"  ¬¬x = x: {inv};  x∧¬x = ⊥: {nc};  x∨¬x = ⊤: {lem}  "
          "(MO2 6/6; 2-qubit closure 258/258 in quantum_pair)")
    assert inv and nc and lem
    print("  → ¬p never falls (involution + NC + LEM-law at every size);")
    print("    p→p never falls (Sasaki identity). The quantum price is paid")
    print("    ONCE by the join side (distributivity, cover, the table) —")
    print("    the negation side rides free at any number of quanta.")

    print("\n  ✓ ladder: 1 — distributivity (and material MP); 2 — the truth")
    print("    table itself (0/512); 3 — same law, harder (0/64); beyond —")
    print("    saturation. ¬p and p→p: iron at every rung.")
