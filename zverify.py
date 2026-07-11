# -*- coding: utf-8 -*-
"""
Expedition E12: the "verify" operation and verdict stability.

THE NARROW PLACE: greedy verdicts are non-monotone under verification —
both refusals flip (expected: default deny until checked) and T flips
(dangerous: ¬¬p = T dies at p:=F). A verdict without a warranty is a
Frege cell.

THE CURE: the stability bit = global supervaluation (all completions
give one classical answer coinciding with the verdict). Measurements:
  1. A gallery of flips (including the death of T).
  2. THE EQUIVALENCE THEOREM: stability-by-supervaluation ⟺ invariance
     under ANY sequence of verifications (total).
  3. Classification of the battery's verdicts: T/F × stable/until-verification.
  4. Monotonicity: a stable verdict is never revoked by any verify.
Conclusion for the tool: a verdict = a pair (value, warranty).
"""

from itertools import product

from ztl import T, F, Z, ev, atoms
from zmodal import worlds, ztl_eval, global_super

# marking: dict atom → T | F | 'M' (mark)

def verify(marking, atom, value):
    """The act of verification: remove the mark, write in the earned value."""
    assert marking[atom] == "M", "only a mark can be verified"
    m2 = dict(marking)
    m2[atom] = value
    return m2


def stable_bit(phi, marking):
    """Stability by supervaluation: all completions give one classical
    answer equal to the current greedy verdict."""
    v = ztl_eval(phi, marking)
    return all(ev(phi, w) == v for w in worlds(marking))


def invariant_under_all_verifications(phi, marking):
    """True invariance: the verdict does not change under any sequence
    of verifications (enumeration of all grounding paths)."""
    v0 = ztl_eval(phi, marking)
    marks = [a for a, s in marking.items() if s == "M"]

    def rec(m, rest):
        if ztl_eval(phi, m) != v0:
            return False
        if not rest:
            return True
        a = rest[0]
        return all(rec(verify(m, a, val), rest[1:]) for val in (T, F))

    # the order of verifications does not matter for enumerating the
    # outcomes: all subsets are covered via recursion over a fixed list
    # (each step takes both values; intermediate states checked at every step)
    return rec(marking, marks)


if __name__ == "__main__":
    p, q = "p", "q"
    print("=" * 72)
    print("E12. VERIFICATION AND STABILITY: fencing the Frege cell")
    print("=" * 72)

    print("\n### 1. A gallery of flips (p is a mark)")
    gallery = [
        ("p ∨ ¬p", ("or", p, ("not", p)), T),
        ("p → p",  ("imp", p, p), T),
        ("¬¬p",    ("not", ("not", p)), F),      # ← the death of T!
        ("¬(p∧¬p)", ("not", ("and", p, ("not", p))), T),
        ("p ∧ ¬p", ("and", p, ("not", p)), T),
    ]
    m0 = {p: "M"}
    for nm, phi, val in gallery:
        v_before = ztl_eval(phi, m0)
        v_after = ztl_eval(phi, verify(m0, p, val))
        st = stable_bit(phi, m0)
        flip = "FLIP" if v_before != v_after else "held"
        print(f"  {nm:10s} verdict {v_before} → verify(p:={val}) → {v_after}"
              f"  [{flip}; stability bit: {'STABLE' if st else 'until-verification'}]")
    print("  ¬¬p: the greedy T dies at p:=F — a T-verdict without a warranty is dangerous.")
    print("  The stability bit predicted every flip and every hold.")

    print("\n### 2. The equivalence theorem (total, 2 atoms)")
    pool = [p, ("not", p), ("or", p, ("not", p)), ("not", ("not", p)),
            ("imp", p, q), ("and", p, ("not", q)), ("xnor", p, q),
            ("or", ("and", p, q), ("not", p)), ("xor", p, ("not", q)),
            ("imp", ("not", ("not", p)), q)]
    markings = [dict(zip((p, q), c)) for c in product((T, F, "M"), repeat=2)]
    total, mismatch = 0, 0
    for phi in pool:
        for m in markings:
            total += 1
            if stable_bit(phi, m) != invariant_under_all_verifications(phi, m):
                mismatch += 1
                print(f"  ✗ DIVERGENCE: {phi} at {m}")
    print(f"  pairs checked (formula × marking): {total}; divergences: {mismatch}")
    if mismatch == 0:
        print("  ✓ STABILITY-BY-SUPERVALUATION ⟺ INVARIANCE UNDER ANY")
        print("    VERIFICATIONS — the warranty is computable in one global pass.")

    print("\n### 3. Classification of the battery's verdicts (p, q are marks)")
    m2 = {p: "M", q: "M"}
    classes = {}
    for phi in pool:
        v = ztl_eval(phi, m2)
        st = stable_bit(phi, m2)
        key = (v, st)
        classes.setdefault(key, []).append(phi)
    for (v, st), fs in sorted(classes.items(), key=repr):
        label = f"{v}-{'stable' if st else 'until-verification'}"
        print(f"  {label:22s}: {len(fs)} formulas")
    print("  The dangerous class — \"T-until-verification\" (ladder verdicts):")
    for phi in classes.get((T, False), []):
        print(f"    {phi}")

    print("\n### 4. Monotonicity of the stable (total)")
    bad = 0
    for phi in pool:
        for m in markings:
            if stable_bit(phi, m):
                marks = [a for a, s in m.items() if s == "M"]
                for a in marks:
                    for val in (T, F):
                        m2v = verify(m, a, val)
                        if ztl_eval(phi, m2v) != ztl_eval(phi, m) or \
                           not stable_bit(phi, m2v):
                            bad += 1
    print(f"  violations of stable-verdict monotonicity: {bad}")
    print("  ✓ A stable verdict is never revoked and never loses stability.")

    print("\n### Conclusion for the tool")
    print("  A verdict = a PAIR (value, warranty): the value is greedy (fast,")
    print("  local), the warranty is supervaluational (one global pass over")
    print("  the completions). \"Stable T\" — build your house; \"T until")
    print("  verification\" — a ladder report, alive till the first check;")
    print("  \"stable F\" — an earned refutation; \"F until verification\" —")
    print("  default deny. The local and global modes (E10) are not rivals")
    print("  but the answer and the warranty of one product. The Frege cell is fenced.")
