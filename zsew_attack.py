# -*- coding: utf-8 -*-
"""
zsew_attack — Arkady's adversarial cases against the E29 seam, run before
any fix, so the failure surface is measured and on the record.

A. Miteiko reviewed the seam sketch (2026-07-21) and named its central
unresolved issue, more fundamental than any Lean proof:

    "What exactly is being sewn? 'Two verdicts' is not a sufficient
     answer. Two unrelated formulas can both evaluate to F without
     agreeing about anything."

He is right, and this file proves it against our own code rather than
conceding it in words. The seam of E29 joins over VERDICT EQUALITY
(xnor = T). The task needs joining over TYPED CLAIM CERTIFICATES with a
shared namespace. Everything the seam gets wrong below flows from that
one substitution — verdict equality standing in for agreement, the
seventeenth instance of the day's shape.

His five distinctions, which the seam collapses into one:
  same result        v_A == v_B                     (what the seam used)
  compatible results both can coexist
  equivalent claims  φ_A ≡ φ_B under a shared schema
  mutually consistent φ_A ∧ φ_B jointly assertable
  agreement          the parties assert the same thing and settle it so

PRE-REGISTERED VERDICTS (what the current seam SHOULD be caught doing):
  #1 same verdict, unrelated formulas  → seam says SEWN (WRONG: manufactures
                                          agreement from equal outputs)
  #2 same atom, different meaning      → seam says CONTRADICTION (may be a
                                          spurious clash from aliasing)
  #3 different atoms, same claim        → seam cannot see the equivalence
  #8 pairwise-compatible, jointly incon → seam is pairwise-only, cannot see
  #10 one party withholds               → seam says CANNOT (CORRECT)

The value of the file is the honest ledger: what the seam gets right,
what it gets wrong, and — decisively — which failures are BUGS in the
verdict-equality join and which are MISSING CAPACITY awaiting the typed
certificate. They are not the same, and a benchmark must distinguish
expected rejection from lack of representational capacity (Arkady).

Run:  python3 zsew_attack.py
"""
import itertools

from zsew import Seam, sew
from zmodal import ztl_eval

T, F, M = "T", "F", "M"


def _atoms(phi, acc=None):
    acc = set() if acc is None else acc
    if isinstance(phi, str):
        acc.add(phi)
    else:
        for s in phi[1:]:
            _atoms(s, acc)
    return acc


def single_gate(A, B):
    """The OLD join: same ground-clash check as sew(), but ↔ ONLY at the
    formula level — no ∧ gate. Isolating the ∧ gate means keeping every
    other check identical, so any difference from sew() is the ∧ gate and
    nothing else."""
    clash = {k for k in A.marking.keys() & B.marking.keys()
             if A.marking[k] != B.marking[k]
             and M not in (A.marking[k], B.marking[k])}
    if clash:
        return "CONTRADICTION"
    m = {**A.marking, **B.marking}
    for k in A.marking.keys() & B.marking.keys():
        m[k] = A.marking[k] if A.marking[k] != M else B.marking[k]
    x = ztl_eval(("xnor", A.formula, B.formula), m)
    d = ztl_eval(("xor", A.formula, B.formula), m)
    if x == T and d == F:
        return "SEWN"
    if x == F and d == T:
        return "CONTRADICTION"
    return "CANNOT"


def jointly_assertable(A, B):
    """Is there a full completion under which BOTH formulas are T? The
    honest notion of 'can coexist', as opposed to 'have equal verdict'."""
    m = {**A.marking, **B.marking}
    atoms = sorted(_atoms(A.formula) | _atoms(B.formula))
    marks = [a for a in atoms if m.get(a, M) == M]
    for combo in itertools.product((T, F), repeat=len(marks)):
        mm = dict(m)
        mm.update(zip(marks, combo))
        if ztl_eval(A.formula, mm) == T and ztl_eval(B.formula, mm) == T:
            return True
    return False


# (label, A, B, what the seam does wrong, class)
CASES = []


def case(label, A, B, klass):
    CASES.append((label, A, B, klass))


case("#1 same verdict, unrelated formulas",
     Seam(("not", "p"), {"p": M}), Seam(("not", "q"), {"q": M}), "BUG")
case("#2 same atom name, opposite verification",
     Seam("p", {"p": T}), Seam("p", {"p": F}), "AMBIGUOUS")
case("#3 different atom names, same intended claim",
     Seam("p", {"p": T}), Seam("r", {"r": T}), "MISSING")
case("#7 different grounds, same conclusion",
     Seam(("or", "p", ("not", "p")), {"p": T}),
     Seam(("or", "q", ("not", "q")), {"q": F}), "MISSING"),
case("#10 one party withholds an answer",
     Seam("p", {"p": T}), Seam("q", {"q": M}), "CORRECT")
case("agreement of two grounded, same claim (the one honest SEWN)",
     Seam("p", {"p": T}), Seam("p", {"p": T}), "CORRECT")


def run():
    print("=" * 78)
    print("ARKADY'S CASES vs THE E29 SEAM — measured before any fix")
    print("=" * 78)
    print("  The seam joins over VERDICT EQUALITY. Where that is not the")
    print("  same as agreement, it is caught here.\n")
    print(f"  {'case':46s}{'↔ only (old)':>14s}{'↔ AND ∧ (now)':>16s}   class")
    bugs, missing, healed = [], [], []
    for label, A, B, klass in CASES:
        old = single_gate(A, B)
        new, _ = sew(A, B)
        flag = "  ← healed" if old != new else ""
        print(f"  {label:46s}{old:>14s}{new:>16s}   {klass}{flag}")
        if klass == "BUG":
            bugs.append(label)
        if klass == "MISSING":
            missing.append(label)
        if old != new:
            healed.append(label)

    print("\n  The decisive #1 — the bug and its cure in one line:")
    A, B = Seam(("not", "p"), {"p": M}), Seam(("not", "q"), {"q": M})
    m = {**A.marking, **B.marking}
    print(f"    ¬p vs ¬q :  ↔ = {ztl_eval(('xnor',A.formula,B.formula),m)} "
          f"(don't conflict)   ∧ = {ztl_eval(('and',A.formula,B.formula),m)} "
          "(not jointly earned)")
    print("      ↔ alone sews them — verdict equality read as agreement, the")
    print("      day's shape once more, and it lies. ∧ refuses them: two")
    print("      claims F by default deny have no ground to stand a")
    print("      conjunction on. LEGAL SEWING MUST SURVIVE ∧ (curator).")

    print(f"\n{'=' * 78}\nTHE LEDGER\n{'=' * 78}")
    print(f"  BUG (unsound join, now healed by ∧) : {len(bugs)}  — "
          f"{'; '.join(bugs)}")
    print(f"  healed by the ∧ gate (its ONLY effect): {len(healed)}  — "
          f"{'; '.join(healed)}")
    print(f"  MISSING (needs the typed certificate): {len(missing)}")
    print("  These are DIFFERENT: a bug is the join manufacturing a wrong")
    print("  answer; missing capacity is the join lacking the certificate")
    print("  fields (namespace, schema version, derivation) to answer at")
    print("  all. A fix addresses the first; only the typed certificate")
    print("  addresses the second.")
    print()
    print("  ROOT CAUSE (Arkady): the seam must join TYPED CLAIM")
    print("  CERTIFICATES over a shared namespace, not bare verdicts. Until")
    print("  the object of composition is defined, SEWN cannot be trusted.")
    print()
    print("  Consequently the E29 claim 'incoherence cannot be silent' is")
    print("  narrowed to: incoherence REPRESENTED in the common vocabulary")
    print("  and supplied to the seam cannot be silently composed by a")
    print("  correct join. It cannot catch misaligned atoms, differing")
    print("  schemas, or a contradiction that lives in reality unrepresented.")

    # the ∧-gate fix (curator, 2026-07-21): #1 must now be refused
    A1, B1 = Seam(("not", "p"), {"p": M}), Seam(("not", "q"), {"q": M})
    st1, _ = sew(A1, B1)
    print(f"\n  AFTER THE ∧-GATE FIX: case #1 (¬p, ¬q) now → {st1}")
    print("    the two-gate seam (↔ AND ∧) refuses to sew two ungrounded")
    print("    claims that merely share a verdict. ↔ passes, ∧ = F, so the")
    print("    seam returns CANNOT — no ground under the agreement.")
    assert st1 == "CANNOT", f"the ∧ gate did not catch #1: got {st1}"
    print("\n  ATTACK GREEN — bug measured, then closed by the ∧ gate.")


if __name__ == "__main__":
    run()
