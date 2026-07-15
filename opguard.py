# -*- coding: utf-8 -*-
"""
opguard — zero-trust for the OPERATION (the applied second floor).

The first floor distrusts DATA (a mark Z on an input). This distrusts the
TRANSFORMATION: a pipeline contains an untrusted operation `?` — a plug-in,
someone else's code, an unaudited rule — whose exact behaviour you have not
verified, only its type (say, a binary connective). Question:

    does the safety property hold no matter what `?` does?

That is the zero-trust reading, one floor up: grant T only if T is FORCED for
every candidate the untrusted operation might be — the worst case over `?`.
`robust(φ)` returns SAFE, or a witness `(?, data)` where the property breaks.

Write the untrusted op as a node `("?", arg1, arg2)`; candidates are the binary
connectives. A property is SAFE iff, for every candidate substituted for `?`,
φ is a tautology over the data.

Example measured below: `?(a,b) → (a∨b)` (an untrusted sanitiser should imply
"clean") is NOT safe — `?=imp` at a=F,b=F outputs T yet a∨b is F: the untrusted
step looks clean while it is not. Whereas `(a ∧ ?(b,c)) → a` is safe — the
conclusion is forced by the verified `a`, whatever `?` does.

Names provisional.
"""

from itertools import product

from ztl import T, F, ev, OPS2

CANDIDATES = list(OPS2)                       # and, or, imp, xor, xnor


def _sub(phi, cand):
    """Replace the untrusted operation ('?', …) with a candidate connective."""
    if isinstance(phi, str):
        return phi
    if phi[0] == "?":
        return (cand,) + tuple(_sub(a, cand) for a in phi[1:])
    return (phi[0],) + tuple(_sub(a, cand) for a in phi[1:])


def _atoms(phi, acc=None):
    acc = set() if acc is None else acc
    if isinstance(phi, str):
        if phi not in (T, F):
            acc.add(phi)
    else:
        for a in phi[1:]:
            _atoms(a, acc)
    return acc


def robust(phi, candidates=CANDIDATES):
    """SAFE iff φ is T for every candidate `?` and every data assignment.
    Returns (True, None) or (False, (breaking_candidate, breaking_env))."""
    atoms = sorted(_atoms(phi))
    for cand in candidates:
        sub = _sub(phi, cand)
        for combo in product((T, F), repeat=len(atoms)):
            env = dict(zip(atoms, combo))
            if ev(sub, env) != T:
                return False, (cand, env)
    return True, None


DEMO = [
    ("grant = a ∧ ?(b,c);  claim grant → a  (never grant without a)",
     ("imp", ("and", "a", ("?", "b", "c")), "a")),
    ("sanitiser: ?(a,b) → (a∨b)  (untrusted step should imply clean)",
     ("imp", ("?", "a", "b"), ("or", "a", "b"))),
    ("weakening: a → (?(x,y) → a)  (a forces the conclusion)",
     ("imp", "a", ("imp", ("?", "x", "y"), "a"))),
    ("?(a,b) → a  (trust the untrusted op to be a projection?)",
     ("imp", ("?", "a", "b"), "a")),
]


if __name__ == "__main__":
    print("opguard — is the property SAFE no matter what the untrusted `?` does?\n")
    for name, phi in DEMO:
        ok, w = robust(phi)
        if ok:
            print(f"  SAFE   {name}")
        else:
            print(f"  UNSAFE {name}\n         breaks at ?={w[0]}, data {w[1]}")
    print("\n  SAFE = the conclusion is forced by verified data whatever `?` is;\n"
          "  UNSAFE = the property leans on what the untrusted operation does.")
