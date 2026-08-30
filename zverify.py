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


def occurs(a, phi):
    """Does atom `a` occur in `phi` at all? Port of ContextClosure.lean:49 —
    negation does NOT clear an occurrence."""
    if isinstance(phi, str):
        return phi == a
    return any(occurs(a, p) for p in phi[1:])


def neg_free(a, phi):
    """`negFree` of ContextClosure.lean:64, ported line for line.

        neg φ    -> !occurs a φ            (occurrence, NOT polarity)
        imp φ ψ  -> !occurs a φ && negFree a ψ
        xor/xnor -> !(occurs a φ || occurs a ψ)

    Those three positions are exactly where a negation reaches the atom. A
    polarity reading would let `¬¬p` into the fragment — the canonical gift,
    T that dies at p:=F. Measured: the first draft here did exactly that."""
    if isinstance(phi, str):
        return True
    op = phi[0]
    if op == "not":
        return not occurs(a, phi[1])
    if op in ("xor", "xnor"):
        return not (occurs(a, phi[1]) or occurs(a, phi[2]))
    if op == "imp":
        return (not occurs(a, phi[1])) and neg_free(a, phi[2])
    return all(neg_free(a, p) for p in phi[1:])


def in_no_gift_fragment(phi, marking):
    """`posMarks` of NoGift.lean:118: every MARKED atom stands outside negation."""
    return all(neg_free(a, phi) for a, s in marking.items() if s == "M")


def _conjuncts(phi):
    """Разложить конъюнкцию в список сомножителей, сколь угодно вложенную."""
    if isinstance(phi, (list, tuple)) and phi and phi[0] == "and":
        return _conjuncts(phi[1]) + _conjuncts(phi[2])
    return [phi]


def _atoms_of(phi):
    if isinstance(phi, str):
        return set() if phi in ("T", "F") else {phi}
    if phi[0] == "not":
        return _atoms_of(phi[1])
    return _atoms_of(phi[1]) | _atoms_of(phi[2])


def f_locked_by_markfree_conjunct(phi, marking):
    """`NoGift.f_locked` (доказана 2026-08-30, ПУСТОЙ СПИСОК АКСИОМ): ложный
    конъюнкт, не содержащий ни одной метки, запирает F — уточнение не может
    его тронуть, а F поглощает конъюнкцию.

    ЗАЧЕМ ЗДЕСЬ. Теорема для T (`no_gift`) закрывает только половину: при F
    расчёт по-прежнему обходил 3^n. Промерено 2026-08-30: 11 оснований — 393 мс,
    13 — 4.1 с, дальше не считается. Эта проверка стоит один проход по
    конъюнктам.

    ЧЕСТНАЯ УЗОСТЬ, и её надо читать вместе с выгодой: на ПЕРВОМ разборе
    нетронутой заявки условие не выполняется никогда — там каждый конъюнкт
    есть голое непроверенное основание, то есть с меткой. Платит со второго
    прохода, когда часть проверок уже сделана."""
    if ztl_eval(phi, marking) != F:
        return False
    for c in _conjuncts(phi):
        if any(marking.get(a) == "M" for a in _atoms_of(c)):
            continue                      # в конъюнкте есть метка — не наш случай
        if ztl_eval(c, marking) == F:
            return True
    return False


def hereditary_bit(phi, marking):
    """The HEREDITARY grade: the verdict is unchanged under every
    partial refinement. This is the true shelf-life warranty; it
    implies the sound grade (completions are refinements).

    SHORTCUT BY THEOREM, added 2026-08-27. `NoGift.no_gift` (kernel-checked,
    empty axiom list — verified by building the module, not by reading its
    docstring):

        refines v w -> posMarks v φ -> evalF v φ = T -> evalF w φ = T

    So a T verdict inside the fragment is hereditary by proof, and the 3^n
    walk over `refinements` is not needed. ONLY T is protected: at F the
    theorem is silent (`F_is_not_protected` — 950 of 1700 in-fragment F cells
    are revocable), so that branch still enumerates.

    MEASURED. Equivalence against the brute force: 26,600 (formula, marking)
    pairs over depth<=2 on three atoms, 2,549 firings, ZERO divergences. On
    chapter 3 of the book (28 marks, 3^28 = 22,876,792,454,961 refinements)
    this turns ~364 days into 0.048 ms.

    The fragment is narrow, and that is not hidden: by the corpus's own
    measurement 66% / 97% / 99% of honest hereditary verdicts sit OUTSIDE it,
    the share rising with depth. This is a shortcut, not a cure."""
    v = ztl_eval(phi, marking)
    if v == T and in_no_gift_fragment(phi, marking):
        return True
    # ВТОРАЯ ПОЛОВИНА, подключена 2026-08-30: `NoGift.f_locked`.
    if v == F and f_locked_by_markfree_conjunct(phi, marking):
        return True
    return all(ztl_eval(phi, m2) == v for m2 in refinements(marking))


def grade(phi, marking):
    """The warranty grade of the current verdict.

    THE MARKING IS CUT TO THE FORMULA'S ATOMS FIRST, and this is a theorem,
    not an optimisation gamble: `evalF_congr` / `frozen` (lean/NoGift.lean,
    empty axiom list) — the value of a formula depends only on the valuation
    of ITS atoms. A refinement of a foreign mark therefore cannot move any
    evaluation of `phi`, so the quantifiers over those marks collapse and
    both bits answer identically on the cut marking.

    Why it matters: callers hand over the marking of a WHOLE document.
    Chapter 3 of the book carries 28 marks while its claim touches 4 atoms,
    none marked — the walk was 3^28 (≈364 days) for an answer the cut
    computes in microseconds. Measured 2026-08-27; the equivalence was also
    checked by brute force against the uncut walk (documents small enough
    to finish): zero divergences."""
    ats = atoms(phi)
    marking = {a: v for a, v in marking.items() if a in ats}
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
    print("  → no depth-1 fence exists for the hereditary grade.")

    print("\n### 6. The fence depth is exactly m−1 (no constant-depth fence)")
    # For SOUND verdicts all full completions agree, so heredity
    # violations can live only at partial refinements of size ≤ m−1:
    # depth m−1 always SUFFICES. It is also NECESSARY: the guard
    # family  (b₁∧…∧b_{m−1}) → (a→a)  — a conjunction guard of m−1
    # marks over the fallen law of identity — is sound, invariant
    # under every verification of fewer than m−1 atoms, and dies when
    # all guards are verified true (the door opens onto the greedy-F
    # gap a→a). Checked deterministically here for m = 3, 4, 5; the
    # m = 2 witness is the (¬p)→(q→q) cell of §5.
    from itertools import combinations
    for m in (3, 4, 5):
        guards = [f"b{i}" for i in range(1, m)]
        atoms = guards + ["a"]
        conj = guards[0]
        for g in guards[1:]:
            conj = ("and", conj, g)
        phi = ("imp", conj, ("imp", "a", "a"))
        mk = {x: "M" for x in atoms}
        v = ztl_eval(phi, mk)
        snd = all(ev(phi, dict(zip(atoms, c))) == v
                  for c in product((T, F), repeat=m))
        inv = all(ztl_eval(phi, {**mk, **dict(zip(ns, vs))}) == v
                  for sz in range(1, m - 1)
                  for ns in combinations(atoms, sz)
                  for vs in product((T, F), repeat=sz))
        dies = ztl_eval(phi, {**mk, **{g: T for g in guards}}) != v
        assert v == T and snd and inv and dies
        print(f"  m={m}: (∧ of {m-1} guards)→(a→a) — sound T, invariant "
              f"below m−1, dies at m−1 ✓")
    print("  → THE FENCE DEPTH IS EXACTLY m−1: sufficient for every sound")
    print("    verdict (violations cannot hide in full completions), and")
    print("    necessary by the guard family. NO constant-depth")
    print("    characterization of the hereditary grade exists; what")
    print("    remains open is a STRUCTURAL (non-enumerative) criterion.")

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
