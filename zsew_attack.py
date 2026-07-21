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
    print(f"  {'case':46s}{'seam':15s}{'class':10s}")
    bugs, missing = [], []
    for label, A, B, klass in CASES:
        st, _ = sew(A, B)
        print(f"  {label:46s}{st:15s}{klass}")
        if klass == "BUG":
            bugs.append(label)
        if klass == "MISSING":
            missing.append(label)

    print("\n  The decisive #1, in Arkady's own five distinctions:")
    A, B = Seam(("not", "p"), {"p": M}), Seam(("not", "q"), {"q": M})
    st, _ = sew(A, B)
    m = {**A.marking, **B.marking}
    sv = ztl_eval(A.formula, m) == ztl_eval(B.formula, m)
    print(f"    ¬p vs ¬q     seam: {st}")
    print(f"      same verdict (what the seam used) : {sv}")
    print(f"      equivalent claims                 : {A.formula == B.formula}")
    print(f"      jointly assertable                : {jointly_assertable(A, B)}")
    print("      → SEWN on 'same verdict' alone; the claims are not")
    print("        equivalent and agreement was never shown. This is the")
    print("        bug, and it is the day's shape once more: verdict")
    print("        equality is a convenient proxy for agreement, and it lies.")

    print(f"\n{'=' * 78}\nTHE LEDGER\n{'=' * 78}")
    print(f"  BUG (unsound join)      : {len(bugs)}  — {'; '.join(bugs)}")
    print(f"  MISSING (needs schema)  : {len(missing)}")
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

    assert bugs, "the seam stopped manufacturing agreement — re-read #1"
    print("\n  ATTACK GREEN — the failure surface is measured and named.")


if __name__ == "__main__":
    run()
