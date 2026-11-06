# -*- coding: utf-8 -*-
"""
Banach–Tarski, judged: "the pieces' volumes add up" is a sentence about volumes the pieces do not have.

Banach and Tarski (1924): a solid ball can be cut into finitely many pieces (five suffice) that, moved only by
rotations and translations, reassemble into two balls each the size of the first. The paradox reads as "volume is
doubled". The standard resolution: the pieces are not measurable, so they have no volume, and the construction needs
the axiom of choice.

THE FORMALISATION, IN WORDS FIRST — a bad skeleton refutes a straw man:
  two claims are mixed in "the ball was doubled":
    DECOMPOSE   "a ball can be cut into finitely many pieces that, rigidly moved, make two balls" — a theorem of ZFC.
                It rests on choice (it fails in Solovay's model of ZF, where every set of reals is measurable, given an
                inaccessible cardinal): an axiom adopted, a STIPULATION, not a fact of the world. Unstipulated: OPEN,
                cure "stipulate AC"; stipulated: EARNED on a declared ground.
    CONSERVE    "the volumes of the pieces add up to the ball's volume, before and after" — needs each piece to HAVE a
                volume. The pieces' heart is a paradoxical decomposition of the free group on two letters, and on that
                group no finitely additive, invariant measure exists: the volumes are not small or large, they are
                ABSENT. "volume(piece)" has no subject — E — and so has the sum.
  So there is no contradiction to resolve: the theorem is earned on its stipulated ground, and the conservation
  argument that would refute it has no subject.

MEASURED HERE (each section asserts what it prints):
  1. the paradoxical decomposition of the free group F2 = <a, b>: with S(x) the reduced words beginning with x,
     F2 = {e} ∪ S(a) ∪ S(a⁻¹) ∪ S(b) ∪ S(b⁻¹) (disjoint), and a·S(a⁻¹) = F2 \\ S(a), b·S(b⁻¹) = F2 \\ S(b) —
     checked word by word on every reduced word up to length 10 (shifts checked where both sides are in range);
  2. no invariant finitely additive probability on F2 respects it: the five masses would have to satisfy
     1 = m_e + m_a + m_a⁻ + m_b + m_b⁻, m_a⁻ = 1 − m_a, m_b⁻ = 1 − m_b, all >= 0 — the exact LP is INFEASIBLE
     (zdegree's simplex); this is the computed ground of the mark E on "volume(piece)";
  3. two rotations of space that generate a free group (the classical pair, rotations by arccos(1/3) about two
     perpendicular axes): no nontrivial reduced word of length <= 8 equals the identity — exact arithmetic in Q(√2)
     (evidence, not the proof; the proof is a reduction mod 3);
  4. the judge: DECOMPOSE with AC unstipulated OPEN ("stipulate"), stipulated EARNED; CONSERVE E (no subject),
     its mark computed in 2; a physical ball of gold (finitely many atoms: every piece measurable) — doubling REFUTED.

NOT CLAIMED: anything new about the theorem; that choice is false. Prior art: Banach & Tarski (Fund. Math. 6, 1924);
Hausdorff (1914); Wagon, "The Banach–Tarski Paradox" (1985); Solovay (Ann. Math. 92, 1970). What is added is the
judge's form: which part is a stipulation, which part has no subject.

Run:  python3 dilemmas/banach_tarski.py
"""
import itertools
import os
import sys
from fractions import Fraction as Fr

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from ztljudge import judge                                    # noqa: E402
import zdegree                                                 # noqa: E402

GEN = ("a", "A", "b", "B")                                     # A = a⁻¹, B = b⁻¹
INV = {"a": "A", "A": "a", "b": "B", "B": "b"}


def reduced_words(n):
    out = [""]
    frontier = [""]
    for _ in range(n):
        nxt = []
        for w in frontier:
            for g in GEN:
                if not w or INV[g] != w[-1]:
                    nxt.append(w + g)
        out += nxt
        frontier = nxt
    return out


def mul(x, w):
    """the reduced word x·w for a one-letter x"""
    return w[1:] if w and w[0] == INV[x] else x + w


def sec1(n=10):
    words = reduced_words(n)
    S = {g: {w for w in words if w[:1] == g} for g in GEN}
    assert set(words) == {""} | S["a"] | S["A"] | S["b"] | S["B"]
    assert sum(len(S[g]) for g in GEN) + 1 == len(words)                     # disjoint
    # x·S(x⁻¹): a word x⁻¹u maps to u, so every word of length <= n - 1 not starting with x is reached from a word
    # of length <= n; compare both sides there
    for x, xi in (("a", "A"), ("b", "B")):
        image = {mul(x, w) for w in S[xi]}
        image = {w for w in image if len(w) <= n - 1}
        want = {w for w in words if len(w) <= n - 1 and w[:1] != x}
        assert image == want, (x, len(image ^ want))
    print(f"   F2 = {{e}} ∪ S(a) ∪ S(a⁻¹) ∪ S(b) ∪ S(b⁻¹), disjoint, on all {len(words)} reduced words of length <= {n};")
    print("   a·S(a⁻¹) = F2 \\ S(a) and b·S(b⁻¹) = F2 \\ S(b): two of the pieces rebuild the whole group, twice")


def sec2():
    # variables m_e, m_a, m_A, m_b, m_B >= 0; invariance turns a·S(a⁻¹) = F2 \ S(a) into m_A = 1 - m_a
    rows = [([1, 1, 1, 1, 1], "=", 1), ([0, 1, 1, 0, 0], "=", 1), ([0, 0, 0, 1, 1], "=", 1)]
    try:
        zdegree.lp_max([0, 0, 0, 0, 0], rows)
        feasible = True
    except zdegree.DegreeError:
        feasible = False
    assert not feasible
    # both sides: drop the invariance rows and a measure exists (the LP is not infeasible by construction)
    zdegree.lp_max([0, 0, 0, 0, 0], rows[:1])
    print("   1 = m_e + m_a + m_a⁻ + m_b + m_b⁻ with m_a + m_a⁻ = 1 and m_b + m_b⁻ = 1 (invariance): the exact LP is")
    print("   INFEASIBLE — no invariant finitely additive probability; without invariance it is feasible (control)")
    return "E" if not feasible else "T"


class Q2:
    """x + y√2 with rational x, y"""
    __slots__ = ("x", "y")

    def __init__(self, x, y=0):
        self.x, self.y = Fr(x), Fr(y)

    def __add__(self, o):
        return Q2(self.x + o.x, self.y + o.y)

    def __mul__(self, o):
        return Q2(self.x * o.x + 2 * self.y * o.y, self.x * o.y + self.y * o.x)

    def __eq__(self, o):
        return self.x == o.x and self.y == o.y

    def __hash__(self):
        return hash((self.x, self.y))


def matmul(P, Q):
    return tuple(tuple(sum((P[i][k] * Q[k][j] for k in range(3)), Q2(0)) for j in range(3)) for i in range(3))


def sec3(n=8):
    c, s = Q2(Fr(1, 3)), Q2(0, Fr(2, 3))                       # cos θ = 1/3, sin θ = 2√2/3
    ms = Q2(0, Fr(-2, 3))
    one, zero = Q2(1), Q2(0)
    Rx = ((one, zero, zero), (zero, c, ms), (zero, s, c))       # about the x axis
    Rz = ((c, ms, zero), (s, c, zero), (zero, zero, one))       # about the z axis
    inv = lambda M: tuple(tuple(M[j][i] for j in range(3)) for i in range(3))   # rotations: inverse = transpose
    mats = {"a": Rx, "A": inv(Rx), "b": Rz, "B": inv(Rz)}
    I = ((one, zero, zero), (zero, one, zero), (zero, zero, one))
    for g in GEN:
        assert matmul(mats[g], mats[INV[g]]) == I
    frontier = {"": I}
    count = 0
    for _ in range(n):
        nxt = {}
        for w, M in frontier.items():
            for g in GEN:
                if not w or INV[g] != w[-1]:
                    W = matmul(M, mats[g])
                    assert W != I, f"the word {w + g} is the identity"
                    nxt[w + g] = W
                    count += 1
        frontier = nxt
    # both sides: the same search on quarter turns (a finite group) MUST find the identity, e.g. a·a·a·a
    q0, q1, qm = Q2(0), Q2(1), Q2(-1)
    Qx = ((q1, q0, q0), (q0, q0, qm), (q0, q1, q0))
    Qz = ((q0, qm, q0), (q1, q0, q0), (q0, q0, q1))
    qmats = {"a": Qx, "A": inv(Qx), "b": Qz, "B": inv(Qz)}
    found = None
    frontier_q = {"": I}
    for _ in range(4):
        nxt = {}
        for w, M in frontier_q.items():
            for g in GEN:
                if not w or INV[g] != w[-1]:
                    W = matmul(M, qmats[g])
                    if W == I and found is None:
                        found = w + g
                    nxt[w + g] = W
        frontier_q = nxt
    assert found is not None
    print(f"   the rotations by arccos(1/3) about x and about z: none of the {count} nontrivial reduced words of")
    print(f"   length <= {n} is the identity (exact in Q(√2)) — evidence the group is free; the proof works mod 3;")
    print(f"   control: quarter turns about the same axes give the identity at once ({found})")


def sec4(volume_mark):
    open_ = judge("decompose", {"decompose": "Z"})
    earned = judge("decompose", {"decompose": "T"})
    conserve = judge("pieces_volumes_add_up", {"pieces_volumes_add_up": volume_mark})
    gold = judge("gold_ball_doubled", {"gold_ball_doubled": "F"})   # finitely many atoms: every piece has a volume
    assert open_["disposition"] == "OPEN" and earned["disposition"] == "EARNED"
    assert conserve["disposition"] == "E" and gold["disposition"] == "REFUTED"
    print(f"   DECOMPOSE, choice unstipulated: {open_['disposition']} (cure: stipulate AC); stipulated: {earned['disposition']}")
    print(f"   CONSERVE (the pieces' volumes add up): {conserve['disposition']} — the mark computed in section 2")
    print(f"   a physical ball of gold doubled: {gold['disposition']} (finitely many atoms: every piece is measurable)")


if __name__ == "__main__":
    print("-" * 72)
    print("1. THE PARADOXICAL DECOMPOSITION OF THE FREE GROUP")
    sec1()
    print("-" * 72)
    print("2. NO VOLUME FOR THE PIECES: NO INVARIANT FINITELY ADDITIVE MEASURE")
    mark = sec2()
    print("-" * 72)
    print("3. THE GROUP SITS INSIDE THE ROTATIONS")
    sec3()
    print("-" * 72)
    print("4. THE JUDGE")
    sec4(mark)
    print("-" * 72)
    print("BANACH-TARSKI: all measurements hold — DECOMPOSE is earned on the stipulated choice, CONSERVE has no subject.")
