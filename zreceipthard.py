# -*- coding: utf-8 -*-
"""
Expedition E59: THE EXACT RECEIPT IS NP-HARD TO KNOW.

`receipt_complete` proves the label never omits a cause; `label_exact_linear`
proves it never names an idle atom on a LINEAR claim; `clash_names_an_idle_atom`
shows `p ∧ ¬p` names one. Open was the boundary: is there a cheap exact rule at
all? `lean/ZReceiptHard.lean` proves, on the empty axiom list, that on

    R_ψ := (a ∨ (ψ ∧ ¬ψ)) ∧ ψ        (ψ not reading a, no constants)

at the all-marked start the receipt names a (`named`), and a is worth naming —
`pivotal` in LabelExact's sense, a reading of the other marks, POSSIBLY PARTIAL,
under which a := T and a := F give different verdicts — exactly when ψ is
satisfiable (`pivotal_iff_sat`). So deciding "named in vain" is deciding SAT: the
exact receipt is NP-hard (membership in NP is argued in prose, not proved, so
"NP-complete" is not claimed), and `labF`'s cheap candidate list is the forced
cut, as `joint` is for the width (E58).

Measured here with the judge's own `_lazy` and `pivotal` read LITERALLY — the
other marks range over {T, F, Z}, not {T, F}. That literal reading is what the
first attempt got wrong: against definite readings `a ∧ ψ` looked like a
reduction; against the kernel's definition it is pivotal for EVERY ψ (T-side Z,
F-side F), which is the negative control below (`conj_always_pivotal`).
"""
import itertools
import random
from ztl import T, F, Z, ev
from ztljudge import _lazy

OPS = ("and", "or", "imp", "xor", "xnor")


def pivotal(phi, m, a, atoms):
    """LabelExact.pivotal, literally: some reading of the OTHER unverified atoms
    (each may stay Z) under which a := T and a := F give different lazy verdicts."""
    others = [x for x in atoms if x != a and m[x] == Z]
    for vals in itertools.product((T, F, Z), repeat=len(others)):
        w = dict(m); w.update(zip(others, vals))
        w1 = dict(w); w1[a] = T
        w2 = dict(w); w2[a] = F
        if _lazy(phi, w1)[0] != _lazy(phi, w2)[0]:
            return True
    return False


def sat(psi, xs):
    return any(ev(psi, dict(zip(xs, vals))) == T
               for vals in itertools.product((T, F), repeat=len(xs)))


def witness(a, psi):
    return ("and", ("or", a, ("and", psi, ("not", psi))), psi)


def formulas(depth, xs):
    if depth == 0:
        return list(xs)
    sub = formulas(depth - 1, xs)
    out, seen = [], set()
    for f in list(sub) + [("not", s) for s in sub] + [(op, p, q) for op in OPS for p in sub for q in sub]:
        if f not in seen:
            seen.add(f); out.append(f)
    return out


def check_pool(pool, xs, label):
    a = "a"
    atoms = [a] + list(xs)
    allZ = {x: Z for x in atoms}
    named = agree = ctrl = 0
    div = 0
    for psi in pool:
        phi = witness(a, psi)
        lv, lab = _lazy(phi, allZ)
        named += (lv == Z and a in lab)
        p, s = pivotal(phi, allZ, a, atoms), sat(psi, xs)
        agree += (p == s)
        ctrl += pivotal(("and", a, psi), allZ, a, atoms)
        if p != s or not (lv == Z and a in lab):
            div += 1
            print(f"  ✗ DIVERGENCE {psi}: named {a in lab}, pivotal {p}, satisfiable {s}")
    n = len(pool)
    print(f"  {label}: {n} formulas ψ; a named on {named}/{n}; 'pivotal ⟺ satisfiable' on {agree}/{n}"
          f" (satisfiable: {sum(sat(psi, xs) for psi in pool)}); divergences {div}")
    print(f"    negative control a ∧ ψ: pivotal on {ctrl}/{n} — no reduction there")
    return div == 0 and ctrl == n


def main():
    print("=" * 72)
    print("E59. THE RECEIPT NAMES a IN VAIN EXACTLY WHEN ψ IS UNSATISFIABLE")
    print("=" * 72)
    xs2 = ["q", "r"]
    ok1 = check_pool(formulas(2, xs2), xs2, "all formulas ψ of depth ≤ 2 over q, r")
    rnd = random.Random(59)
    xs3 = ["q", "r", "s"]

    def rf(d):
        if d == 0 or rnd.random() < 0.2:
            return rnd.choice(xs3)
        op = rnd.choice(["not"] + list(OPS))
        return ("not", rf(d - 1)) if op == "not" else (op, rf(d - 1), rf(d - 1))
    ok2 = check_pool([rf(3) for _ in range(600)], xs3, "600 random formulas ψ of depth ≤ 3 over q, r, s (seed 59)")
    print("\n  Reading: a is on the receipt on every witness; it was worth naming exactly")
    print("  when ψ has a classical point. Deciding 'named in vain' decides SAT.")
    ok = ok1 and ok2
    print("\n" + ("E59 GREEN: pivotal ⟺ satisfiable on every witness, and a ∧ ψ is never a reduction"
                  if ok else "E59 RED"))
    return 0 if ok else 1


if __name__ == "__main__":
    import sys
    sys.exit(main())
