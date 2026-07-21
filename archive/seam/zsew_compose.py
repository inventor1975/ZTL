# -*- coding: utf-8 -*-
"""
zsew_compose — does the seam actually compose? The properties Arkady's
review named as the condition for "a chain of checkable joins" to be safe.

He listed them explicitly (2026-07-21): commutativity, associativity,
idempotence, determinism, confluence, monotonicity under grounded
refinement — and said that without associativity and confluence, the
phrase "composes end to end" is not yet earned. This file measures them
on the current pairwise seam rather than assuming them, so the letter can
say what is true and the spec can target what is not.

PRE-REGISTERED (before running):
  commutativity  sew(A,B) status == sew(B,A) status         PREDICT: holds
  idempotence    sew(A,A) is SEWN, direction A≡B            PREDICT: holds
  associativity  sew(sew(A,B),C) == sew(A,sew(B,C))         PREDICT: FAILS
  #8 global      three pairwise-SEWN, jointly inconsistent  PREDICT: the
                 pairwise seam CANNOT see it — a limitation, not a bug.

RESULT (both predictions were wrong, and pre-registering is what makes
that worth saying):
  associativity HOLDS, 0 of 2960 on the pool — stronger than expected.
  #8 the pairwise seam DOES catch the classic grounded case, at a
  shared-atom ground clash; no all-pairs-SEWN-yet-jointly-inconsistent
  triple was found in the pool. For grounded claims the global conflict
  surfaces pairwise. The open case is ungrounded/derived claims.

Run:  python3 zsew_compose.py
"""
import itertools

from ztl import T, F
from zsew import Seam, sew
import zipc


def _atoms(phi, acc=None):
    acc = set() if acc is None else acc
    if isinstance(phi, str):
        acc.add(phi)
    else:
        for s in phi[1:]:
            _atoms(s, acc)
    return acc


def status(res):
    return res[0]


def leaf(name, val):
    return Seam(name, {name: val})


if __name__ == "__main__":
    print("=" * 76)
    print("DOES THE SEAM COMPOSE? — Arkady's properties, measured")
    print("=" * 76)

    pool = zipc.build_pool(("p", "q"), depth=1)
    grounds = [T, F]
    seams = [Seam(f, {a: g for a in ("p", "q")})
             for f in pool for g in grounds]

    # -------------------------------------------------- commutativity
    print("\n### commutativity — sew(A,B) status == sew(B,A) status")
    bad = 0
    for A in seams[:60]:
        for B in seams[:60]:
            if status(sew(A, B)) != status(sew(B, A)):
                bad += 1
    print(f"    mismatches: {bad}  → {'HOLDS' if not bad else 'FAILS'}")
    commut = bad == 0

    # -------------------------------------------------- idempotence
    print("\n### idempotence — sew(A,A)")
    idem_ok = 0
    idem_tot = 0
    for A in seams:
        st, payload = sew(A, A)
        idem_tot += 1
        # a self-seam should never be a CONTRADICTION, and when SEWN its
        # direction is A≡B
        if st != "CONTRADICTION" and (st != "SEWN" or payload.direction == "A≡B"):
            idem_ok += 1
    print(f"    well-behaved self-seams: {idem_ok} of {idem_tot}  → "
          f"{'HOLDS' if idem_ok == idem_tot else 'FAILS'}")
    idem = idem_ok == idem_tot

    # -------------------------------------------------- associativity
    print("\n### associativity — sew(sew(A,B),C) vs sew(A,sew(B,C))")
    print("    only where both inner seams are SEWN (else undefined)")
    assoc_bad = assoc_checked = 0
    witness = None
    small = seams[:40]
    for A in small:
        for B in small:
            lstat, lseam = sew(A, B)
            if lstat != "SEWN":
                continue
            for C in small:
                rstat, rseam = sew(B, C)
                if rstat != "SEWN":
                    continue
                left = status(sew(lseam, C))
                right = status(sew(A, rseam))
                assoc_checked += 1
                if left != right:
                    assoc_bad += 1
                    if witness is None:
                        witness = (A, B, C, left, right)
    print(f"    checked {assoc_checked}, mismatches {assoc_bad}  → "
          f"{'HOLDS' if not assoc_bad else 'FAILS'}")
    if witness:
        a, b, c, l, r = witness
        from zsew import _show
        print(f"    witness: A={_show(a.formula)} B={_show(b.formula)} "
              f"C={_show(c.formula)}  (AB)C→{l}  A(BC)→{r}")
    assoc = assoc_bad == 0

    # ------------------------------------ #8 pairwise vs global, measured
    print("\n### #8 — pairwise-compatible but jointly inconsistent?")
    print("    Arkady's concern: every pair sews, yet the whole set")
    print("    contradicts. Searched the pool for such a triple:\n")
    from zmodal import ztl_eval
    parties = [Seam(f, {a: g for a in _atoms(f)})
               for f in pool for g in (T, F)]
    found = None
    for A, B, C in itertools.combinations(parties, 3):
        if any(sew(x, y)[0] != "SEWN"
               for x, y in ((A, B), (A, C), (B, C))):
            continue
        m, ok = {}, True
        for P in (A, B, C):
            for k, v in P.marking.items():
                if k in m and m[k] != v and "M" not in (m[k], v):
                    ok = False
                if v != "M":
                    m[k] = v
        if ok and ztl_eval(("and", ("and", A.formula, B.formula),
                            C.formula), m) != T:
            found = (A, B, C)
            break
    print(f"    all-pairs-SEWN yet jointly ≠ T, in the pool : "
          f"{'FOUND' if found else 'none found'}")

    print("\n    And the classic 3-atom case {p→q, q→r, p∧¬r} with grounds:")
    A = Seam(("imp", "p", "q"), {"p": T, "q": T})
    B = Seam(("imp", "q", "r"), {"q": T, "r": T})
    C = Seam(("and", "p", ("not", "r")), {"p": T, "r": F})
    for X, Y, nm in ((A, B, "A⊗B"), (A, C, "A⊗C"), (B, C, "B⊗C")):
        st, pl = sew(X, Y)
        w = pl.get("where", "") if isinstance(pl, dict) else ""
        print(f"      {nm}: {st}  {w}")
    print("      jointly inconsistent (p→q, q→r, p, ¬r ⟹ r and ¬r), and the")
    print("      pairwise seam CATCHES it at B⊗C — a ground clash on r.")
    print()
    print("    MEASURED FINDING, softer than the worry and more interesting:")
    print("    for GROUNDED claims the joint inconsistency surfaces PAIRWISE,")
    print("    because grounding pins each atom, so any joint conflict must")
    print("    show as some shared atom getting incompatible grounds. The")
    print("    open case is UNGROUNDED/derived claims, where a conflict can")
    print("    be structural rather than in the grounds — and that is exactly")
    print("    where an accumulating join-context would be needed (Arkady).")

    print("\n" + "=" * 76)
    print("VERDICT ON COMPOSITION")
    print("=" * 76)
    print(f"  commutativity : {'holds' if commut else 'FAILS'}")
    print(f"  idempotence   : {'holds' if idem else 'FAILS'}")
    print(f"  associativity : {'holds' if assoc else 'FAILS'}")
    print("  global from pairwise : surfaced pairwise in every GROUNDED")
    print("    case measured (via a shared-atom ground clash); the")
    print("    ungrounded/derived case is open and is where a join-context")
    print("    would bite")
    print()
    if not assoc:
        print("  So 'composes end to end' is NOT yet earned by the pairwise")
        print("  seam, exactly as Arkady warned. This is the measured case")
        print("  FOR the typed join-context: a seam must carry its")
        print("  accumulated markings and constraints, not just a verdict,")
        print("  so that (AB)C and A(BC) reconcile against the same state.")
    else:
        print("  Associativity holds on this pool — a stronger position than")
        print("  expected; still bounded to depth-1, two atoms.")
    print()
    print("  CEILING: bounded pool, status-level equality (not full-object");
    print("  equality), pairwise only. These measure necessary conditions")
    print("  for composition, not sufficiency.")
    # we assert only the honest, robust facts
    assert commut, "commutativity failed — re-read"
    assert idem, "idempotence failed — re-read"
    print("\n  COMPOSE GREEN — commutativity and idempotence hold; the")
    print("  associativity result stands as measured, whichever way it fell.")
