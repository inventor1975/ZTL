# -*- coding: utf-8 -*-
"""
MARK SENSITIVITY: how many compound formulas can tell "unverified" from "false".

CLASSIC-VS-ZTL.md carried the figure "1263 of 2924 (43%)" from 2026-09-18 with
no definition beside it and no script anywhere in the tree that produced it.
Both halves of that are defects: the number is true only of a NARROWER reading
than the sentence it stood under, and an unnamed run is not evidence. This
instrument is the missing run. Measured 2026-09-19.

The pool is the depth<=2 regression pool over p, q and the six connectives,
built exactly as in paper/core_logic_checks.py: 2926 formulas, of which 2924
are compound.

Three readings of "distinguishes unverified from false", and they differ:

  ONE MARK    the mark sits on one designated atom, the other is verified:
              exists b in {T,F} with  phi(Z,b) != phi(F,b)              -> 1263
  EITHER      the union of the two one-mark readings                    -> 1830
  MARK-SENSITIVE (the paper's definition, sec. "What the mark buys"):
              on SOME valuation, replacing EVERY mark by false changes
              the verdict                                               -> 1840

The ten formulas that only the third reading sees are the ones that need BOTH
atoms unverified at once -- e.g. ((p->p) v (q->q)), which is F when both atoms
carry the mark and T as soon as either is verified. Marking one atom at a time
cannot reach them, which is exactly why the one-mark count understates.

Under the engineering default (unverified := false) the count is 0 by
construction, and that zero is the point: the substitution merges the two
inputs, so nothing downstream can ever separate them again.
"""
import itertools

from ztl import T, F, Z, NOT, AND, OR, IMP, XOR, XNOR

OPS = {"not": NOT, "and": AND, "or": OR, "imp": IMP, "xor": XOR, "xnor": XNOR}
SYM = {"and": "∧", "or": "∨", "imp": "→", "xor": "⊕", "xnor": "↔"}
V = [T, F, Z]


def ev(phi, env):
    if isinstance(phi, str):
        return env[phi]
    if phi[0] == "not":
        return OPS["not"](ev(phi[1], env))
    return OPS[phi[0]](ev(phi[1], env), ev(phi[2], env))


def show(phi):
    if isinstance(phi, str):
        return phi
    if phi[0] == "not":
        return "¬" + show(phi[1])
    return "(" + show(phi[1]) + SYM[phi[0]] + show(phi[2]) + ")"


def pool():
    """The depth<=2 regression pool, verbatim from paper/core_logic_checks.py."""
    d1 = ["p", "q"] + [("not", x) for x in ("p", "q")] + \
         [(o, a, b) for o in ("and", "or", "imp", "xor", "xnor")
          for a in ("p", "q") for b in ("p", "q")]
    d2 = [(o, a, b) for o in ("and", "or", "imp", "xor", "xnor")
          for a in d1 for b in d1] + \
         [("not", x) for x in d1 if not isinstance(x, str)]
    return d1 + d2


def one_mark(phi, atom):
    """Mark on `atom` alone, the other atom verified."""
    other = "q" if atom == "p" else "p"
    return any(ev(phi, {atom: Z, other: b}) != ev(phi, {atom: F, other: b})
               for b in (T, F))


def either_mark(phi):
    return one_mark(phi, "p") or one_mark(phi, "q")


def mark_sensitive(phi):
    """The paper's definition: on SOME valuation, replacing every mark by
    false changes the verdict."""
    for a, b in itertools.product(V, repeat=2):
        env = {"p": a, "q": b}
        if Z not in (a, b):
            continue
        subst = {k: (F if v == Z else v) for k, v in env.items()}
        if ev(phi, env) != ev(phi, subst):
            return True
    return False


def main():
    ok = True

    def check(cond, msg):
        nonlocal ok
        print(("  ✓ " if cond else "  ✗ ") + msg)
        if not cond:
            ok = False

    p = pool()
    comp = [f for f in p if not isinstance(f, str)]
    print("1. the pool")
    check(len(p) == 2926, f"pool size {len(p)}")
    check(len(comp) == 2924, f"compounds {len(comp)}")

    print("2. how many compounds separate the mark from false")
    n_p = sum(1 for f in comp if one_mark(f, "p"))
    n_q = sum(1 for f in comp if one_mark(f, "q"))
    n_either = sum(1 for f in comp if either_mark(f))
    n_sens = sum(1 for f in comp if mark_sensitive(f))
    check(n_p == 1263, f"ONE MARK on p (q verified): {n_p} of 2924 = {100*n_p/2924:.1f}%")
    check(n_q == 1263, f"ONE MARK on q (p verified): {n_q} of 2924 = {100*n_q/2924:.1f}%")
    check(n_either == 1830, f"EITHER (union of the two): {n_either} of 2924 = {100*n_either/2924:.1f}%")
    check(n_sens == 1840, f"MARK-SENSITIVE (the paper's): {n_sens} of 2924 = {100*n_sens/2924:.1f}%")

    print("3. what the one-mark reading cannot reach: both atoms unverified at once")
    only_both = [f for f in comp if mark_sensitive(f) and not either_mark(f)]
    check(len(only_both) == 10, f"{len(only_both)} compounds need BOTH marks")
    for f in sorted(only_both, key=lambda g: len(show(g)))[:3]:
        env_zz = {"p": Z, "q": Z}
        env_ff = {"p": F, "q": F}
        print(f"     {show(f):24s}  both marked: {ev(f, env_zz)}   both false: {ev(f, env_ff)}")

    print("4. the same question asked of the engineering default (unverified := false)")
    # NOT a measurement: asking a formula to separate the two inputs AFTER the
    # substitution has merged them would compare an expression with itself, and
    # such a zero measures nothing. The content is upstream, in the map: the
    # substitution sends the marked input and the false input to the SAME
    # environment, so 0 of 2924 follows by construction. That is what we check.
    def subst(env):
        return {k: (F if v == Z else v) for k, v in env.items()}

    merged = [(a, b) for a, b in itertools.product(V, repeat=2) if Z in (a, b)]
    collapses = all(subst({"p": a, "q": b}) == subst(subst({"p": a, "q": b}))
                    and subst({"p": a, "q": b})
                    == subst({"p": F if a == Z else a, "q": F if b == Z else b})
                    for a, b in merged)
    check(collapses and len(merged) == 5,
          f"the substitution merges all {len(merged)} marked valuations into unmarked ones — "
          "0 of 2924 can separate them, by construction and not by luck")

    print("5. the shortest separators are ordinary formulas")
    short = sorted({show(f) for f in comp if mark_sensitive(f)}, key=lambda s: (len(s), s))[:5]
    check(len(short[0]) <= 3, f"shortest: {', '.join(short)}")

    print()
    print(f"MARK SENSITIVITY GREEN: {n_sens} of 2924 mark-sensitive (63%), "
          f"{n_p} of 2924 with one atom marked (43%)" if ok else "MARK SENSITIVITY RED")
    return 0 if ok else 1


if __name__ == "__main__":
    import sys
    sys.exit(main())
