# -*- coding: utf-8 -*-
"""
zmodid — E33: MODAL IDENTITY — necessity of identity and rigid designation.

Kripke (1971): identity, once it holds, holds necessarily — a = b ⊨ □(a=b).
Classically this follows from Leibniz's law plus □(a=a). ZTL now has both
identity (E31, zeq.py) and a modal layer (§17, zmodal.py: worlds are the
completions of the unverified). This stand crosses them, and the mark turns
out to be the single locus where rigidity — and with it the necessity of
identity — breaks.

THE MODEL. A world is a completion that RESOLVES every unverified
reference: it assigns a grounded referent to each marked name. A grounded
name denotes itself in every world (a RIGID designator); a marked name's
referent VARIES across worlds (NON-rigid). Within a world everything
denotes, so identity there is classical T/F. Then

    □(x=y)  =  x,y have the same referent in EVERY completion,
    ◇(x=y)  =  ... in SOME completion.

FINDINGS (measured total):

  1. Grounded names are RIGID; a marked name is NOT. This is the whole
     source of contingency.
  2. NECESSITY OF IDENTITY holds for earned identities: whenever the
     zero-trust verdict eqI(x,y) = T (so x,y are grounded and the same),
     □(x=y) = T. Kripke, recovered. Where a reference is unverified the
     equality is never T, so the law is vacuous there — the mark yields no
     necessary identity because it yields no identity at all.
  3. NECESSITY OF DISTINCTNESS likewise: eqI(x,y)=F ⟹ □(x≠y).
  4. CONTINGENT IDENTITY lives exactly on the mark: for a marked name m and
     a grounded a, ◇(m=a) ∧ ◇(m≠a) — possible but not necessary.
  5. RIGID DESIGNATION IS THE MODAL FACE OF EXISTENCE. A name is rigid iff
     it denotes iff E!(t)=T (earned self-identity, E32). Existence, rigidity
     and earned self-identity are one property seen three ways.
  6. THE SUPERVALUATION DIVERGENCE, on identity. In every completion a
     marked name denotes SOMETHING equal to itself, so □(m=m) = T — self-
     identity is super-true. But ZTL's actual verdict is eqI(m,m) = Z. ZTL
     is no more supervaluational about identity than about excluded middle
     (§17, and the LEM divergence of §25): it MARKS the unearned rather
     than completing it.

Run:  python3 zmodid.py
"""
import os
import sys
from itertools import product

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from ztl import T, F, Z                                          # noqa: E402

GROUND = ("a", "b", "c")            # grounded individuals (rigid names)
MARKED = ("m1", "m2")               # unresolved references (non-rigid names)
NAMES = GROUND + MARKED

# a world = a grounded referent for each marked name
WORLDS = [dict(zip(MARKED, combo))
          for combo in product(GROUND, repeat=len(MARKED))]


def ref(name, w):
    """The referent of a name in world w."""
    return w[name] if name in MARKED else name


def eqW(x, y, w):
    """Identity inside a world — classical, everything denotes there."""
    return T if ref(x, w) == ref(y, w) else F


def box_eq(x, y):
    return T if all(eqW(x, y, w) == T for w in WORLDS) else F


def dia_eq(x, y):
    return T if any(eqW(x, y, w) == T for w in WORLDS) else F


def eqI(x, y):
    """The zero-trust verdict (E31): Z if a reference is unverified."""
    if x in MARKED or y in MARKED:
        return Z
    return T if x == y else F


def Ebang(t):
    """Existence = earned self-identity (E32)."""
    return eqI(t, t)


def rigid(name):
    """A name is rigid if its referent is the same in every world."""
    return len({ref(name, w) for w in WORLDS}) == 1


if __name__ == "__main__":
    print("=" * 76)
    print("E33 — MODAL IDENTITY: necessity of identity and rigid designation")
    print("=" * 76)
    print(f"  grounded {GROUND} (rigid), marked {MARKED} (unresolved); "
          f"{len(WORLDS)} completions\n")

    # ---------------------------------------------------- 1. rigidity
    print("### 1. Grounded names are rigid; marked names are not")
    for n in NAMES:
        print(f"    {n}: rigid = {rigid(n)}"
              + ("" if n in GROUND else "   (referent varies by completion)"))
    assert all(rigid(g) for g in GROUND), "a grounded name was non-rigid"
    assert not any(rigid(m) for m in MARKED), "a marked name was rigid"

    # ------------------------------------------- 2. necessity of identity
    print("\n### 2. Necessity of identity — a=b ⊨ □(a=b), for earned identity")
    bad = 0
    licensed = 0
    for x in NAMES:
        for y in NAMES:
            if eqI(x, y) == T:
                licensed += 1
                if box_eq(x, y) != T:
                    bad += 1
    print(f"    eqI(x,y)=T ⟹ □(x=y)=T : {bad} violations of {licensed} earned "
          f"identities → {'HOLDS' if bad == 0 else 'FAILS'}")
    assert bad == 0, "necessity of identity failed for an earned identity"
    print("    Kripke recovered: an earned identity is necessary. The mark")
    print("    licenses none (eqI never T through an unverified reference).")

    # --------------------------------------- 3. necessity of distinctness
    print("\n### 3. Necessity of distinctness — a≠b ⊨ □(a≠b)")
    bad_d = 0
    lic_d = 0
    for x in NAMES:
        for y in NAMES:
            if eqI(x, y) == F:
                lic_d += 1
                if dia_eq(x, y) == T:     # possible to be equal → not nec. distinct
                    bad_d += 1
    print(f"    eqI(x,y)=F ⟹ □(x≠y) : {bad_d} violations of {lic_d} earned "
          f"distinctnesses → {'HOLDS' if bad_d == 0 else 'FAILS'}")
    assert bad_d == 0, "necessity of distinctness failed for an earned case"

    # ------------------------------------------ 4. contingent identity
    print("\n### 4. Contingent identity lives on the mark")
    witness = None
    for x in NAMES:
        for y in NAMES:
            if x != y and dia_eq(x, y) == T and box_eq(x, y) == F:
                witness = (x, y)
                break
        if witness:
            break
    x, y = witness
    print(f"    ◇({x}={y}) = {dia_eq(x,y)},  □({x}={y}) = {box_eq(x,y)}"
          f"  → possible but not necessary")
    print(f"    and at least one of {x},{y} is a marked reference: "
          f"{x in MARKED or y in MARKED}")
    assert witness is not None, "no contingent identity found"
    assert (x in MARKED or y in MARKED), "contingency arose without a mark"

    # ------------------------------- 5. rigidity = existence = self-identity
    print("\n### 5. Rigid designation is the modal face of existence")
    for n in NAMES:
        print(f"    {n}: rigid={rigid(n)}  E!={Ebang(n)}  "
              f"(rigid ⟺ E!=T: {rigid(n) == (Ebang(n) == T)})")
    assert all(rigid(n) == (Ebang(n) == T) for n in NAMES), \
        "rigidity and existence came apart"
    print("    a name is rigid ⟺ it denotes ⟺ its self-identity is earned.")

    # --------------------------------- 6. the supervaluation divergence
    print("\n### 6. Supervaluation divergence, on identity")
    for m in MARKED:
        print(f"    □({m}={m}) = {box_eq(m,m)}  (super-true: {m} is self-"
              f"identical in every completion)")
        print(f"    eqI({m},{m}) = {eqI(m,m)}  (ZTL's actual verdict)")
    assert all(box_eq(m, m) == T for m in MARKED), "□(m=m) was not super-true"
    assert all(eqI(m, m) == Z for m in MARKED), "eqI(m,m) was not Z"
    print("    □(m=m)=T yet eqI(m,m)=Z — ZTL is NOT supervaluational about")
    print("    identity, exactly as §17 and the LEM divergence of §25.")

    print("\n" + "=" * 76)
    print("WHAT E33 ADDS")
    print("=" * 76)
    print("  Modal identity. Grounded names are rigid designators, so the")
    print("  necessity of identity (Kripke) and of distinctness hold for")
    print("  every EARNED (in)equality. The marked reference is the unique")
    print("  locus of non-rigidity and of contingent identity. Rigidity,")
    print("  existence and earned self-identity are one property (§24/§25).")
    print("  And once more ZTL parts from supervaluation: the completions")
    print("  make a non-denoting name necessarily self-identical, but ZTL")
    print("  marks it rather than granting the verdict.")
    print("\n  ZMODID GREEN — necessity of identity for the earned; the mark is")
    print("  where rigidity breaks; ZTL ≠ supervaluation on identity too.")
