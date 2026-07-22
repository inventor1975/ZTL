# -*- coding: utf-8 -*-
"""
proof_ring — ZTL as a proof-checking ring, over an UNCHANGED core, via ztljudge.

Here ZTL judges a piece of META-logic, not itself: an external arithmetic
proof, 2 + 3 = 5, done the way a child does it — by tally.

    1.  5      = 1+1+1+1+1
    2.  2 + 3  = 5 ?
    3.  2 = 1+1,   3 = 1+1+1
    4.  (1+1) + (1+1+1)  =  1+1+1+1+1
    5.  ∎

The proof is a RING: the left side 2+3 unfolds to five tallies, the right
side 5 unfolds to five tallies, and the two arms MEET at the common tally
`11111`. Soldering the ring is gluing the two arms by `=` (the equality
connective, ZTL's ↔). The ring closes iff both arms reached the same tally.

What ZTL knows, and does not. The atoms below (`two_is_11`, `flatten`, …)
are ARITHMETIC facts, handed in as grounded inputs. ZTL cannot see a number;
it does not compute 2+3. It certifies the LOGICAL ring that combines those
facts — congruence and transitivity of the reductions — and it enforces the
one rule that makes it a check and not a rubber stamp: no link may be taken
on credit. Leave a single reduction unverified (Z) and the ring will not
close. That is ZTL proving the proof, not the arithmetic, and not itself.

Run:  python3 proof_ring.py
"""
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ztljudge import check, join                                    # noqa: E402
from ztl import T, F, Z                                            # noqa: E402

# The five arithmetic facts of the proof, as opaque propositional atoms.
# Each is TRUE (T) when that identity holds; ZTL never sees the numbers.
FACTS = {
    "two_is_11":      "2 = 1+1",
    "three_is_111":   "3 = 1+1+1",
    "sum_subst":      "2+3 = (1+1)+(1+1+1)",      # substitute the two above
    "flatten":        "(1+1)+(1+1+1) = 11111",    # associativity: five tallies
    "five_is_11111":  "5 = 11111",
}

# The two arms of the ring, written for ztljudge's formalizer.
LEFT = "two_is_11 & three_is_111 & sum_subst & flatten"   # 2+3 ⇝ 11111
RIGHT = "five_is_11111"                                    # 5   ⇝ 11111


def ring(marking):
    """Solder the two arms into the ring by `=` and report whether it closes.
    The ring closes as a PROOF only when both arms are grounded-true and their
    equality is earned — a mark or a falsehood leaves it open."""
    j = join(LEFT, RIGHT, "=", marking)
    closed = (j["left"]["verdict"] == T and j["right"]["verdict"] == T
              and j["verdict"] == T)
    return j, closed


def _banner(s):
    print("\n" + s)
    print("-" * len(s))


def main():
    print("=" * 76)
    print("proof_ring — ZTL solders an external proof into a ring: 2 + 3 = 5")
    print("=" * 76)
    print("\nthe proof, by tally:")
    for name, meaning in FACTS.items():
        print(f"    {meaning:28s}   (atom {name})")
    print(f"\n    left  arm: 2+3  ⇝  11111     [{LEFT}]")
    print(f"    right arm: 5    ⇝  11111     [{RIGHT}]")

    all_true = {k: T for k in FACTS}

    # --- 1. every reduction verified: the ring closes -----------------------
    _banner("1. every reduction verified — solder the ring")
    j, closed = ring(all_true)
    print(f"    left  {j['left']['formula']}")
    print(f"          → {j['left']['verdict']}  ({j['left']['grade']})")
    print(f"    right {j['right']['formula']} → {j['right']['verdict']}  "
          f"({j['right']['grade']})")
    print(f"    solder by = :  {j['joined_formula']}")
    print(f"          → {j['verdict']}  ({j['grade']})")
    print(f"\n    RING {'CLOSED' if closed else 'OPEN'} — "
          f"{'2 + 3 = 5 confirmed inside ZTL' if closed else 'not confirmed'}")

    # --- 2. one reduction left unverified: the ring will not close ----------
    _banner("2. one reduction NOT verified (flatten = Z) — zero trust")
    one_missing = {k: T for k in FACTS if k != "flatten"}   # flatten stays Z
    j2, closed2 = ring(one_missing)
    print(f"    left  {j2['left']['formula']}")
    print(f"          → {j2['left']['verdict']}  ({j2['left']['grade']})"
          f"   unverified: {j2['left']['unverified']}")
    print(f"    right → {j2['right']['verdict']}")
    print(f"    solder by = :  → {j2['verdict']}  ({j2['grade']})")
    print(f"      {j2['reading']}")
    print(f"\n    RING {'CLOSED' if closed2 else 'OPEN'} — a single "
          f"unverified link and ZTL will not close it on credit")

    # --- 3. solder the WRONG target (claim 2+3 = 6): the ring resists -------
    _banner("3. solder a false target (5 replaced by 6) — the ring resists")
    # the right arm now asserts the FALSE '6 = 11111'; mark it F
    j3 = join(LEFT, "six_is_11111", "=", dict(all_true, six_is_11111=F))
    closed3 = (j3["left"]["verdict"] == T and j3["right"]["verdict"] == T
               and j3["verdict"] == T)
    print(f"    left  → {j3['left']['verdict']}   "
          f"right (6 = 11111) → {j3['right']['verdict']}")
    print(f"    solder by = :  → {j3['verdict']}  ({j3['grade']})")
    print(f"\n    RING {'CLOSED' if closed3 else 'OPEN'} — the ring closes "
          f"for 5, not for 6")

    # the grade tells WHY each open ring is open — the sharp distinction
    _banner("what the grade distinguishes")
    print(f"    unverified link : left grade = {j2['left']['grade']:20s}"
          "  (open because NOT YET CHECKED)")
    print(f"    false target    : ring grade = {j3['grade']:20s}"
          "  (open because CHECKED AND FALSE)")
    print("    ZTL separates 'not established' from 'refuted' — the mark is "
          "not a truth value.")

    # honest self-check
    assert closed,      "the true proof must close the ring"
    assert not closed2, "an unverified link must leave the ring open"
    assert not closed3, "a false target must leave the ring open"
    print("\n" + "=" * 76)
    print("PROOF-RING GREEN — ZTL confirmed the META-logic of 2+3=5: the ring")
    print("closes when every arithmetic link is grounded, and refuses to close")
    print("on an unverified link or a false target. ZTL judged the proof, not")
    print("the arithmetic, and not itself.")


if __name__ == "__main__":
    main()
