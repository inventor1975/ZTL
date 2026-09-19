# -*- coding: utf-8 -*-
"""
The parameter that is not yours: System 1 computes with X it gets from
System 2.

Nobody on System 1's side has verified X, and System 2 is free to change
it whenever it likes — between two reads, in the middle of a request, for
reasons System 1 will never hear about. The question is not philosophical
and every engineer has met it:

    WHAT MAY SYSTEM 1 STILL CONCLUDE FROM X?

Classical logic has no answer, and not because it is weak. To compute at
all it must put a value in X's place, and putting a value there is
assuming something System 2 never promised. Whichever value is chosen,
the choice is the analyst's, not the data's.

THREE READINGS OF "UNVERIFIED", AND THEY ARE NOT THE SAME (measured
below, and the difference is the point of this stand):

  SUBSTITUTED  X is given a default. One value for the whole formula,
               chosen by us. Every classical law survives — because we
               invented the fact that makes it survive.
  STABLE       X has some definite value; we just do not know which.
               One value for the whole formula, chosen by the world.
               This is the supervaluation reading.
  NOT OURS     X is read where it appears, and System 2 may have changed
               it in between. No value is promised to persist. This is
               ZTL's reading, and it is the only one that matches what
               System 2 is actually entitled to do.

The gap between STABLE and NOT OURS is exactly the price of assuming the
other system holds still for you.

Run:  python3 dilemmas/dirty_param.py
"""
import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import ztl                                                    # noqa: E402
from audit import EQUALITIES, VALIDITIES                      # noqa: E402

T, F, Z = ztl.T, ztl.F, ztl.Z
OPS = {"not": ztl.NOT, "and": ztl.AND, "or": ztl.OR,
       "imp": ztl.IMP, "xor": ztl.XOR, "xnor": ztl.XNOR}
failures = []


def ev(phi, env):
    if phi in ("T", "F"):
        return T if phi == "T" else F
    if isinstance(phi, str):
        return env[phi]
    if phi[0] == "not":
        return OPS["not"](ev(phi[1], env))
    return OPS[phi[0]](ev(phi[1], env), ev(phi[2], env))


def atoms_of(phi, acc=None):
    acc = set() if acc is None else acc
    if isinstance(phi, str):
        if phi not in ("T", "F"):
            acc.add(phi)
    else:
        for x in phi[1:]:
            atoms_of(x, acc)
    return acc


def check(cond, msg):
    print(("  ✓ " if cond else "  ✗ ") + msg)
    if not cond:
        failures.append(msg)


def holds(law, values):
    """Does the law hold when every atom takes the given value? `values`
    maps atom -> value, and a value of Z means: read where it appears,
    System 2 may have changed it in between."""
    if len(law) == 3:                       # an equality: lhs = rhs
        _, lhs, rhs = law
        names = sorted(atoms_of(lhs) | atoms_of(rhs))
        env = {n: values[n] for n in names}
        return ev(lhs, env) == ev(rhs, env)
    _, phi = law                            # a validity: phi = T
    names = sorted(atoms_of(phi))
    return ev(phi, {n: values[n] for n in names}) == T


def survives_ztl(law):
    """ONE foreign parameter: X is unverified, every other atom is System
    1's own and verified. This is the scene — and it is a NARROWER question
    than audit.py asks, which is why the two print different numbers. Both
    are true; the denominators differ, and a number without its definition
    beside it is how a count gets quoted as the opposite of itself."""
    names = sorted(atoms_of(law[1]) |
                   (atoms_of(law[2]) if len(law) == 3 else set()))
    others = [n for n in names if n != "p"]
    for combo in itertools.product((T, F), repeat=len(others)):
        values = dict(zip(others, combo))
        values["p"] = Z
        if not holds(law, values):
            return False
    return True


def survives_ztl_any(law):
    """ANY parameter may be foreign — every atom ranges over T, F and
    unverified. This is audit.py's question, and its answer is the one
    quoted in the paper."""
    names = sorted(atoms_of(law[1]) |
                   (atoms_of(law[2]) if len(law) == 3 else set()))
    for combo in itertools.product((T, F, Z), repeat=len(names)):
        if not holds(law, dict(zip(names, combo))):
            return False
    return True


def survives_stable(law):
    """X has SOME definite value; we do not know which. One value for the
    whole formula — the supervaluation reading."""
    names = sorted(atoms_of(law[1]) |
                   (atoms_of(law[2]) if len(law) == 3 else set()))
    for combo in itertools.product((T, F), repeat=len(names)):
        if not holds(law, dict(zip(names, combo))):
            return False
    return True


def main():
    laws = [(l[0], l[1], l[2]) for l in EQUALITIES] + \
           [(l[0], l[1]) for l in VALIDITIES]
    print("=" * 74)
    print("THE PARAMETER THAT IS NOT YOURS — what System 1 may still conclude")
    print("=" * 74)

    print("\n1. What classical logic can do with an unverified X")
    # Not a measurement dressed up as one: classical valuations range over
    # {T,F}, so there is no classical value that MEANS "not verified". The
    # count is 0 by construction, and the mechanism is worth showing rather
    # than asserting: the two careful defaults are both available and they
    # disagree on the very first law.
    lem = ("or", "p", ("not", "p"))
    print(f"     classical values available for X: {['T', 'F']} — none of them"
          " means 'not verified'")
    print(f"     default X:=F  ->  X∨¬X = {ev(lem, {'p': F})}"
          f"        default X:=T  ->  X∨¬X = {ev(lem, {'p': T})}")
    check(True, "laws classical logic may apply to an UNVERIFIED X: 0 — it "
                "cannot take the input at all")

    print("\n2. The 26 classical laws, with X coming from System 2")
    alive = [l for l in laws if survives_ztl(l)]
    dead = [l for l in laws if not survives_ztl(l)]
    any_alive = [l for l in laws if survives_ztl_any(l)]
    check(len(laws) == 26, f"laws in the battery: {len(laws)}")
    check(len(alive) == 14,
          f"ONE foreign parameter (X from System 2, the rest yours and "
          f"verified): {len(alive)} usable, {len(dead)} refuted")
    check(len(any_alive) == 12,
          f"ANY parameter may be foreign (audit.py's question, the paper's "
          f"figure): {len(any_alive)} usable, {len(laws) - len(any_alive)} refuted")
    print("     Two true counts of two different questions. The more of your")
    print("     input comes from elsewhere, the fewer laws you keep — 14 with")
    print("     one foreign parameter, 12 when any of them may be.")
    print("     usable, first four:")
    for name, *_ in alive[:4]:
        print(f"       {name}")
    print("     refuted, first four — these are the inferences that quietly")
    print("     assume the data is yours:")
    for name, *_ in dead[:4]:
        print(f"       {name}")

    print("\n3. STABLE versus NOT OURS — the price of assuming System 2 holds still")
    stable = [l for l in laws if survives_stable(l)]
    only_if_stable = [l for l in stable if not survives_ztl(l)]
    check(len(stable) == 26,
          f"laws that hold if X is merely UNKNOWN but fixed: {len(stable)} of 26")
    check(len(only_if_stable) == 12,
          f"laws that need X to STAY PUT between two reads: {len(only_if_stable)}")
    print("     So those twelve are not lost to ignorance — ignorance alone")
    print("     costs nothing, all 26 survive it. They are lost to the other")
    print("     system's right to change its mind, which is a different thing")
    print("     and the one System 1 cannot legislate away.")

    print("\n4. The sentence everyone believes is free")
    check(ev(lem, {"p": Z}) == F,
          f"X ∨ ¬X with X from System 2:  {ev(lem, {'p': Z})}   "
          f"(classically always {ev(lem, {'p': T})})")
    check(ev(("xnor", "p", "p"), {"p": Z}) == F,
          f"X = X  with X from System 2:  {ev(('xnor', 'p', 'p'), {'p': Z})}")
    check(ev(("imp", "p", "p"), {"p": Z}) == F,
          f"X → X  with X from System 2:  {ev(('imp', 'p', 'p'), {'p': Z})}")
    print("     Read X twice and nobody promised it was the same X. That is not")
    print("     scepticism, it is the contract System 2 actually offers.")
    back = all(ev(lem, {"p": v}) == T and ev(("xnor", "p", "p"), {"p": v}) == T
               for v in (T, F))
    check(back, "verify X and all three come back to T — classical, cell for cell")

    print()
    if failures:
        print(f"DIRTY-PARAM RED — {len(failures)} check(s) failed")
        return 1
    print("DIRTY-PARAM GREEN — with ONE parameter owned by another system,")
    print("14 of the 26 classical laws still apply and 12 are refuted with a")
    print("witness; when ANY parameter may be foreign it is 12 and 14. Classical")
    print("logic applies 0 either way, having no value that means 'unverified'.")
    print("All 26 survive if X is merely unknown but FIXED — so the refuted ones")
    print("are the exact price of System 2's right to change X between two reads.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
