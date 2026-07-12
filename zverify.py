# -*- coding: utf-8 -*-
"""
Expedition E12: the "verify" operation and verdict warranties.

THE NARROW PLACE: greedy verdicts are non-monotone under verification —
both refusals flip (expected: default deny until checked) and T flips
(dangerous: ¬¬p = T dies at p:=F). A verdict without a warranty is a
Frege cell.

THE CURE — REVISED 2026-07-12 (the E21 find, measured in zopsets.py and
cross-checked here): the warranty is a LADDER OF TWO GRADES, not one bit.

  * SOUND (the old stability bit; supervaluation): every completion
    gives one classical answer equal to the current greedy verdict.
    Buys: "never lies" — a sound verdict agrees with every possible
    resolution of the marks. Cheap: one pass over the completions.
  * HEREDITARY: the verdict is unchanged under EVERY partial refinement
    (any subset of marks verified to any classical values). Buys:
    "never spoils" — no verification path can revoke it. Costlier:
    a pass over the refinements. Hereditary ⟹ sound (completions are
    refinements); the converse is FALSE.

The original E12 claim — "stability-by-supervaluation ⟺ invariance
under any verifications" (90/90) — was POOL-RELATIVE: true on the
original 10-formula pool, falsified by the or(ladder, gap) shape,
e.g. ¬¬p ∨ (q∨¬q): greedy T via the ¬¬ ladder, insured by a gap that
is true in ALL completions yet greedy-F; verifying p:=F kicks the
ladder before the gap closes. This file now MEASURES the separation
instead of the equivalence — the honest ledger:
  1. A gallery of flips (including the death of T), with grades.
  2. THE LADDER: hereditary ⟹ sound total; sound ⇏ hereditary —
     witnesses exhibited (the old equivalence falsified).
  3. Classification: T/F × hereditary / sound-only / until-verification.
  4. Monotonicity: hereditary is never revoked and never loses its
     grade (total); sound-only CAN be revoked — counted.
Conclusion for the tool: a verdict = a pair (value, warranty GRADE).
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
    """The SOUND grade (supervaluation): all completions give one
    classical answer equal to the current greedy verdict. Guarantees
    the verdict never lies about any resolution of the marks; does NOT
    guarantee it survives intermediate verifications (see hereditary_bit)."""
    v = ztl_eval(phi, marking)
    return all(ev(phi, w) == v for w in worlds(marking))


def refinements(marking):
    """All partial refinements: any subset of the marks verified to any
    classical values (the marking itself included). Subset-closed, so
    order-free — this replaces the old fixed-order path recursion."""
    marks = [a for a, s in marking.items() if s == "M"]
    for combo in product(("M", T, F), repeat=len(marks)):
        m2 = dict(marking)
        m2.update(zip(marks, combo))
        yield m2


def hereditary_bit(phi, marking):
    """The HEREDITARY grade: the verdict is unchanged under every
    partial refinement. This is the true shelf-life warranty; it
    implies the sound grade (completions are refinements)."""
    v = ztl_eval(phi, marking)
    return all(ztl_eval(phi, m2) == v for m2 in refinements(marking))


def grade(phi, marking):
    """The warranty grade of the current verdict."""
    if hereditary_bit(phi, marking):
        return "hereditary"
    if stable_bit(phi, marking):
        return "sound"
    return "until-verification"


if __name__ == "__main__":
    p, q = "p", "q"
    print("=" * 72)
    print("E12. VERIFICATION AND WARRANTIES: fencing the Frege cell")
    print("     (revised: the warranty is a two-grade ladder — the E21 find)")
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
        flip = "FLIP" if v_before != v_after else "held"
        print(f"  {nm:10s} verdict {v_before} → verify(p:={val}) → {v_after}"
              f"  [{flip}; warranty: {grade(phi, m0)}]")
    print("  ¬¬p: the greedy T dies at p:=F — a T-verdict without a warranty is dangerous.")

    # the extended pool: the original ten + the or(ladder, gap) cells
    pool = [p, ("not", p), ("or", p, ("not", p)), ("not", ("not", p)),
            ("imp", p, q), ("and", p, ("not", q)), ("xnor", p, q),
            ("or", ("and", p, q), ("not", p)), ("xor", p, ("not", q)),
            ("imp", ("not", ("not", p)), q),
            ("or", ("not", ("not", p)), ("or", q, ("not", q))),   # the cell
            ("imp", ("not", p), ("imp", q, q))]                   # the simpler cell
    markings = [dict(zip((p, q), c)) for c in product((T, F, "M"), repeat=2)]

    print("\n### 2. The ladder (total, extended pool incl. the E21 cells)")
    total = her_not_sound = sound_not_her = 0
    exhibits = []
    for phi in pool:
        for m in markings:
            total += 1
            s, h = stable_bit(phi, m), hereditary_bit(phi, m)
            her_not_sound += (h and not s)
            if s and not h:
                sound_not_her += 1
                if len(exhibits) < 2 and ztl_eval(phi, m) == T \
                        and all(v == "M" for v in m.values()):
                    exhibits.append((phi, m))
    print(f"  pairs checked (formula × marking): {total}")
    print(f"  hereditary without sound: {her_not_sound} (must be 0 — "
          f"hereditary ⟹ sound, completions are refinements)")
    print(f"  sound without hereditary: {sound_not_her} (> 0 — THE GRADES "
          f"SEPARATE;")
    print("   the original E12 equivalence claim was pool-relative, falsified):")
    for phi, m in exhibits:
        m2 = verify(m, p, F)
        print(f"    {phi}: verdict {ztl_eval(phi, m)} sound at all-marks, "
              f"dies to {ztl_eval(phi, m2)} at p:=F")
    assert her_not_sound == 0 and sound_not_her > 0

    print("\n### 3. Classification of the battery's verdicts (p, q are marks)")
    m2 = {p: "M", q: "M"}
    classes = {}
    for phi in pool:
        key = (ztl_eval(phi, m2), grade(phi, m2))
        classes.setdefault(key, []).append(phi)
    for (v, g), fs in sorted(classes.items(), key=repr):
        print(f"  {v}-{g:18s}: {len(fs)} formulas")
    print("  The dangerous classes: \"T-until-verification\" (ladder verdicts)")
    print("  and now \"T-sound\" — true in every completion, yet the verdict")
    print("  can still stall to refusal mid-verification:")
    for phi in classes.get((T, "sound"), []):
        print(f"    sound-only: {phi}")

    print("\n### 4. Monotonicity, per grade (total)")
    her_bad = sound_revoked = 0
    for phi in pool:
        for m in markings:
            marks = [a for a, s in m.items() if s == "M"]
            for a in marks:
                for val in (T, F):
                    m2v = verify(m, a, val)
                    changed = ztl_eval(phi, m2v) != ztl_eval(phi, m)
                    if hereditary_bit(phi, m) and \
                            (changed or not hereditary_bit(phi, m2v)):
                        her_bad += 1
                    if stable_bit(phi, m) and not hereditary_bit(phi, m) \
                            and changed:
                        sound_revoked += 1
    print(f"  hereditary: revocations or grade losses: {her_bad} (must be 0)")
    print(f"  sound-only: revocations under a single verify: {sound_revoked} "
          f"(> 0 — sound buys truth, not shelf life)")
    assert her_bad == 0 and sound_revoked > 0
    print("  ✓ A hereditary verdict is never revoked and never loses its grade.")

    print("\n### 5. The hereditary grade is NOT depth-1 testable")
    # The overnight hunt of 2026-07-12 (151.8M formula-marking pairs,
    # 4 atoms, depth 3) confirmed the ladder totally (hereditary⟹sound
    # and hereditary monotonicity: 0 violations) and killed the cheap-
    # characterization conjecture: one-step invariance does NOT imply
    # heredity. The deterministic trophy cell, kept under regression:
    phi4 = ("imp", ("xnor", "d", ("not", "c")),
            ("imp", ("imp", "b", "a"), ("xnor", "b", "c")))
    m4 = {"a": F, "b": "M", "c": "M", "d": "M"}
    v4 = ztl_eval(phi4, m4)
    marks4 = [a for a, s in m4.items() if s == "M"]
    one_step = all(ztl_eval(phi4, {**m4, a: val}) == v4
                   for a in marks4 for val in (T, F))
    two_step = ztl_eval(phi4, {**m4, "b": F, "d": F})
    print(f"  cell (d↔¬c)→((b→a)→(b↔c)) at a=F, b=c=d marked: verdict {v4}")
    print(f"  invariant under EVERY single verification: {one_step}")
    print(f"  killed by the pair b:=F, d:=F → {two_step}")
    assert v4 == T and one_step and two_step != v4 \
        and not hereditary_bit(phi4, m4)
    print("  → no depth-1 fence exists for the hereditary grade: the")
    print("    roadmap's open question (a cheap characterization) is")
    print("    narrowed — any answer must look at least two moves deep.")

    print("\n### Conclusion for the tool")
    print("  A verdict = a PAIR (value, warranty GRADE), and the grades are a")
    print("  ladder: HEREDITARY T — build your house (no verification path")
    print("  can revoke it); SOUND T — never a lie (every completion agrees)")
    print("  but may stall to refusal before verification completes; T UNTIL")
    print("  VERIFICATION — a ladder report, alive till the first check; the")
    print("  same three grades for F (sound F — an earned-in-all-completions")
    print("  refutation; F until verification — default deny). The Frege cell")
    print("  is fenced by the TOP grade only; the middle grade fences lying,")
    print("  not spoiling. Discovered by the identity atoms of VR Part II (E21).")
