# -*- coding: utf-8 -*-
"""
The Burali-Forti paradox, judged: "the set of all ordinals" escapes every universe it is looked for in.

Burali-Forti (1897), in Cantor's terms: the ordinals are well-ordered, so if they formed a set Ω, Ω would itself be an
ordinal, greater than every ordinal — greater than itself. In ZF the resolution is that there is no such set: the
ordinals form a proper class. In naive set theory, where every property defines a set, the definition loops.

THE FORMALISATION, IN WORDS FIRST — a bad skeleton refutes a straw man:
  two claims share the words "the set of all ordinals":
    EXISTS      "the ordinals of a universe form a set of that universe" — a matter of fact in each universe, and
                false in every one (measured below on the finite universes V_k);
    NAIVE       "Ω is an ordinal" read through naive comprehension: Ω is an ordinal exactly when it is not a member
                of itself (an ordinal is well-founded), and Ω is a member of itself exactly when it is an ordinal (it
                contains every ordinal) — a loop with one negation: the passport office reads it as a PARADOX,
                refusal PERMANENT, as it reads Russell's set.

MEASURED HERE (each section asserts what it prints):
  1. the von Neumann universes V_k (V_0 = {}, V_{k+1} = all subsets of V_k), k = 1..5 (65 536 sets at k = 5):
     the ordinals of V_k (transitive sets, linearly ordered by membership) are exactly 0, 1, ..., k−1; their
     collection is the ordinal k — an ordinal, and NOT a member of V_k. Every universe misses exactly the set
     the paradox asks for;
  2. the judge: "Ω is a set of the universe", its mark computed in section 1: REFUTED; the naive definition through
     the passport office: PARADOX, the claim's credit UNREDEEMABLE.

NOT CLAIMED: anything new about the paradox. Prior art: Burali-Forti (1897); von Neumann's ordinals (1923); the
proper-class resolution of ZF/NBG. What is added is the judge's form, and the measurement that the missing set is
missing in every finite universe in the same way.

Run:  python3 dilemmas/burali_forti.py
"""
import os
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from ztljudge import judge                                    # noqa: E402
import zfl                                                     # noqa: E402

EMPTY = frozenset()


def universes(kmax):
    V = [frozenset()]                                          # V_0 = {} (as the set of its members: none)
    for _ in range(kmax):
        prev = V[-1]
        members = list(prev)
        subsets = []
        for mask in range(1 << len(members)):
            subsets.append(frozenset(members[i] for i in range(len(members)) if mask >> i & 1))
        V.append(frozenset(subsets))
    return V


def is_ordinal(x):
    """von Neumann: transitive, and linearly ordered by membership (well-foundedness is automatic for these sets)"""
    if any(not (y <= x) for y in x):                           # transitive: every member is a subset
        return False
    xs = list(x)
    for i, a in enumerate(xs):
        for b in xs[i + 1:]:
            if not (a in b or b in a):
                return False
    return True


def von_neumann(n):
    o = EMPTY
    for _ in range(n):
        o = o | {o}
    return o


def sec1(kmax=5):
    V = universes(kmax)
    misses = {}
    for k in range(1, kmax + 1):
        ords = {x for x in V[k] if is_ordinal(x)}
        assert ords == {von_neumann(i) for i in range(k)}, k
        omega_k = frozenset(ords)
        assert omega_k == von_neumann(k) and is_ordinal(omega_k)
        assert omega_k not in V[k]
        misses[k] = omega_k not in V[k]
        print(f"   V_{k}: {len(V[k]):>5} sets; its ordinals are 0..{k - 1}; their collection is the ordinal {k} — "
              f"in V_{k}: {omega_k in V[k]}")
    # both sides: the ordinal k IS in the next universe — the collection is a perfectly good set, one level up
    assert all(von_neumann(k) in V[k + 1] for k in range(1, kmax))
    print("   control: the ordinal k is in V_(k+1) — the collection exists, one universe up, never in its own")
    return "F" if all(misses.values()) else "T"


def sec2(mark):
    exists = judge("omega_is_a_set_of_the_universe", {"omega_is_a_set_of_the_universe": mark})
    doc = {"rows": [{"name": "omega_ordinal", "status": "defined", "ground": "~omega_in_omega",
                     "means": "the set of all ordinals is an ordinal (it is not a member of itself)"},
                    {"name": "omega_in_omega", "status": "defined", "ground": "omega_ordinal",
                     "means": "it is a member of itself (it contains every ordinal)"}],
           "claim": "omega_ordinal"}
    r = zfl.run(zfl.coerce(doc))
    assert r["ok"]
    kinds = [p["kind"] for p in r["report"]["passport"]]
    assert exists["disposition"] == "REFUTED"
    assert kinds == ["PARADOX"] and r["report"]["judge"].get("credit") == "UNREDEEMABLE"
    print(f"   'Ω is a set of the universe' (mark computed in 1): {exists['disposition']}")
    print(f"   the naive definition, through the passport office: {kinds[0]}, the claim's credit "
          f"{r['report']['judge']['credit']} — as for Russell's set")


if __name__ == "__main__":
    print("-" * 72)
    print("1. EVERY FINITE UNIVERSE MISSES THE SET OF ITS OWN ORDINALS")
    mark = sec1()
    print("-" * 72)
    print("2. THE JUDGE")
    sec2(mark)
    print("-" * 72)
    print("BURALI-FORTI: all measurements hold — the set of all ordinals is missing from every universe; naively, a loop.")
