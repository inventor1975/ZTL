# -*- coding: utf-8 -*-
"""
zdesc — E32: FREE LOGIC and definite DESCRIPTIONS under the zero-trust lift.

Classical logic assumes every singular term denotes. Free logic drops that
assumption; its three schools disagree on what an atomic statement about a
NON-DENOTING term is worth:

    negative free logic  : FALSE
    positive free logic  : some are TRUE (e.g. self-identity)
    supervaluational     : a truth-value GAP (but excluded middle stays
                           SUPER-true)

ZTL gives a fourth, principled answer that no prior school gives: a
non-denoting term makes the atomic statement **Z** — on credit, reference
unverified — and the greedy lift then propagates it. This is the native
home of Z: a description that has not been shown to denote is exactly an
"unverified until verification".

THE SPINE — existence is EARNED SELF-IDENTITY (Quine, "no entity without
identity", made literal on top of E31):

        E!(t)  :=  eqI(t, t)          (zeq.py)

A grounded reference is equal to itself, so E! = T; an unresolved
reference is not certified equal to itself (E31 refl_marked), so E! = Z.
ZTL therefore never ASSERTS non-existence (a free F); it MARKS it. This is
the zero-trust reading of "exists".

DESCRIPTIONS. ιx.φ(x) — "the x such that φ" — denotes the unique grounded
individual satisfying φ (uniqueness is decided by =, so E32 stands on
E31); with zero or several satisfiers the description is a marked
(non-denoting) reference. Russell rendered "the F is G" as ∃x(Fx ∧
unique ∧ Gx), FALSE when nothing is the F; ZTL diverges — G(ιx.Fx) is Z.

MEASURED DIVERGENCES (this is where ZTL is not any existing free logic):
  * LEM on a non-denoting atom is F in ZTL, SUPER-true in supervaluation.
  * an atomic P(τ) is Z in ZTL, F in negative free logic.
  * greedy propagation: P(τ) alone is Z, but P(τ) ∨ (guarded tautology)
    is T — the mark evaporates in a compound.
  * 1/0 = ιx.(0·x = 1) has no grounded x, so it is a marked reference and
    "1/0 = 1/0" is Z — dead-on with E8 (zarith.py), an internal witness.
  * free-logic UNIVERSAL INSTANTIATION: ∀xφ ⊨ φ(t) FAILS for a
    non-denoting t (the classical law), and the repaired law ∀xφ, E!t ⊨
    φ(t) holds.

Run:  python3 zdesc.py
"""
import os
import sys
from itertools import combinations

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from ztl import T, F, Z, NOT, AND, OR, IMP, XNOR                # noqa: E402

GROUND = ("a", "b", "c")            # the grounded individuals of the domain
MARK = "⊥"                          # the single non-denoting reference token


# ------------------------------------------------------------ descriptions
def iota(phi):
    """The definite description ιx.φ(x): the unique grounded x with φ(x)=T,
    else a non-denoting (marked) reference. φ is a predicate over grounded
    individuals returning T/F. Uniqueness uses equality (E31)."""
    sat = [g for g in GROUND if phi(g) == T]
    return sat[0] if len(sat) == 1 else MARK


def denotes(t):
    return t in GROUND


# ------------------------------------------------------- atoms and equality
def eqI(s, t):
    """Zero-trust identity on resolved terms (E31)."""
    if not denotes(s) or not denotes(t):
        return Z
    return T if s == t else F


def Ebang(t):
    """Existence = earned self-identity (Quine, on top of E31)."""
    return eqI(t, t)


def atom(P, t):
    """A generic atomic predicate P (a set of grounded individuals) applied
    to a term: Z if the term does not denote."""
    if not denotes(t):
        return Z
    return T if t in P else F


# a guarded tautology, ZTL-valid at every value (E26): ¬q → ¬q  ≡ T
GUARD = T


if __name__ == "__main__":
    print("=" * 76)
    print("E32 — FREE LOGIC and definite DESCRIPTIONS, zero-trust")
    print("=" * 76)
    print(f"  grounded domain {GROUND}; non-denoting reference {MARK!r}\n")

    # the running example: "the present king of France" — nobody is king
    KingOf = lambda g: F                      # no grounded individual is king
    theKing = iota(KingOf)                     # ιx.King(x)
    Bald = {"a"}                               # 'a' is bald (an arbitrary P)

    # ------------------------------------------------ 1. non-denoting → Z
    print("### 1. A statement about a non-denoting term is Z (not F, not gap)")
    v = atom(Bald, theKing)
    print(f"    ιx.King(x) denotes: {denotes(theKing)}  → 'the King is Bald' = {v}")
    assert theKing == MARK and v == Z, "the non-denoting atom was not Z"
    print("    negative free logic would say F; supervaluation, a gap; ZTL: Z.")

    # ------------------------------------------------ 2. LEM diverges
    print("\n### 2. Excluded middle on a non-denoting atom — the sharp divergence")
    lem = OR(v, NOT(v))
    print(f"    (King is Bald) ∨ ¬(King is Bald) = {lem}   [ZTL]")
    print(f"    supervaluational free logic: SUPER-TRUE (T on every "
          f"precisification)")
    assert lem == F, "LEM on the non-denoting atom was not F"
    print("    → ZTL is NOT supervaluational: it marks the gap rather than")
    print("      completing it. LEM is F, because the mark is not a value.")

    # ------------------------------------------------ 3. greedy propagation
    print("\n### 3. Greedy propagation — the mark evaporates in a compound")
    alone = atom(Bald, theKing)
    compound = OR(atom(Bald, theKing), GUARD)
    print(f"    'King is Bald'            = {alone}   (on credit)")
    print(f"    'King is Bald ∨ ⊤guard'   = {compound}   (greedy: OR(Z,T)=T)")
    assert alone == Z and compound == T, "greedy propagation broke"
    print("    a non-denoting term poisons only the atom, never a compound.")

    # ------------------------------------------------ 4. Russell divergence
    print("\n### 4. Russell's analysis (F) vs ZTL (Z)")
    # Russell: 'the F is G' = ∃x(Fx ∧ ∀y(Fy→y=x) ∧ Gx)
    def russell(Fp, Gp):
        for x in GROUND:
            if Fp(x) == T and all((Fp(y) != T) or (y == x) for y in GROUND) \
               and Gp(x) == T:
                return T
        return F
    russell_val = russell(KingOf, lambda g: atom(Bald, g))
    ztl_val = atom(Bald, theKing)
    print(f"    Russell 'the King is Bald' = {russell_val}  (∃-unique-∧, FALSE)")
    print(f"    ZTL     'the King is Bald' = {ztl_val}  (marked reference)")
    assert russell_val == F and ztl_val == Z, "the Russell divergence moved"
    print("    same sentence, different verdict: Russell asserts falsity,")
    print("    ZTL refuses the assertion and marks it.")

    # ------------------------------------------------ 5. existence = self-id
    print("\n### 5. Existence is earned self-identity (Quine, on E31)")
    for t in GROUND + (MARK,):
        print(f"    E!({t}) = {Ebang(t)}   (eqI({t},{t}) = {eqI(t,t)})"
              + ("  — never asserted absent, only marked" if t == MARK else ""))
    assert all(Ebang(t) == eqI(t, t) for t in GROUND + (MARK,)), \
        "E! is not eqI(t,t)"
    assert Ebang(MARK) == Z and all(Ebang(g) == T for g in GROUND)
    print("    E!(t) ⟺ eqI(t,t)=T, total — a thing exists iff it is self-identical.")

    # ------------------------------------------------ 6. 1/0 witness
    print("\n### 6. 1/0 = ιx.(0·x = 1) — the internal witness (E8/zarith)")
    Recip0 = lambda g: F                        # no grounded x solves 0·x = 1
    oneOverZero = iota(Recip0)
    print(f"    1/0 denotes: {denotes(oneOverZero)}  → '1/0 = 1/0' = "
          f"{eqI(oneOverZero, oneOverZero)}")
    assert oneOverZero == MARK and eqI(oneOverZero, oneOverZero) == Z, \
        "1/0 self-identity was not Z"
    print("    matches zarith E8 exactly: identity on a marked value is Z.")

    # ------------------------------------------------ 7. free-logic UI
    print("\n### 7. Universal instantiation is free — classical UI fails")
    # ∀x φ(x) over the GROUNDED domain = strict T (quantifiers.py convention)
    def forall(phi):
        return T if all(phi(g) == T for g in GROUND) else F
    Everything = lambda g: T                    # φ true of every grounded thing
    uni = forall(Everything)
    # classical UI to the non-denoting term:
    ui_classical = IMP(uni, atom(set(GROUND), theKing))
    # repaired free-logic UI: ∀xφ ∧ E!t ⊨ φ(t)
    prem = AND(uni, Ebang(theKing))
    ui_repaired_holds = not (prem == T and atom(set(GROUND), theKing) != T)
    print(f"    ∀x φ(x) = {uni};  classical ∀xφ → φ(theKing) = {ui_classical}"
          f"  (FAILS: T→Z=F)")
    print(f"    repaired  ∀xφ, E!t ⊨ φ(t): holds = {ui_repaired_holds}  "
          f"(premise ∧E!t is {prem}, never designated for a non-denoting t)")
    assert ui_classical == F, "classical UI did not fail on the non-denoting term"
    assert ui_repaired_holds, "the repaired free-logic UI failed"
    print("    the free-logic signature: quantifiers range over what EXISTS,")
    print("    and existence is the earned self-identity of §5.")

    print("\n" + "=" * 76)
    print("WHAT E32 ADDS")
    print("=" * 76)
    print("  ZTL is now a FREE LOGIC — and a NEW one. Where negative free")
    print("  logic says F, positive says T, and supervaluation leaves a gap")
    print("  completed by a super-true excluded middle, ZTL MARKS the non-")
    print("  denoting term: the atom is Z, LEM is F, and the mark evaporates")
    print("  greedily in any compound. Existence is earned self-identity")
    print("  (Quine, literally E!(t)=eqI(t,t) on top of E31); descriptions")
    print("  denote by earned uniqueness; 1/0 lands on E8. The nearest")
    print("  ancestor is Kleene's partial logic (undefined = the third value)")
    print("  — ZTL's delta is that the mark is greedy, so a non-denoting term")
    print("  inside a tautology-shaped compound still collapses to a verdict.")
    print("\n  ZDESC GREEN — free logic added; non-denoting → Z, existence = self-identity.")
