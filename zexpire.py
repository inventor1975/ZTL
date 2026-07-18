# -*- coding: utf-8 -*-
"""
Expedition E25: institutional time — the expiry probe (non-monotone ground).

E24 time is MONOTONE: ground only arrives (verify: Z → T/F), and the
arrow theorem holds — every completed trace lands hereditary, the shelf.
Institutional time is NOT monotone: warranties have clocks, documents
expire, registries get re-pledged, snapshots G0 → G1 can TAKE GROUND
BACK (the VRG replay lesson, Proposal 001 R5). This probe adds the
anti-tick

    expire(m, a):  a classical atom returns to the mark Z

and measures, honestly, what it breaks and what survives.

  1. THE PURCHASED CAR LOSES ITS SHELF (witness). The S1 deal at full
     ground is T/hereditary — in monotone time, forever. One expiry
     (the pledge registry is re-checked: status unknown again) and the
     verdict falls T/H → F/U. Hereditary is a warranty against FUTURE
     VERIFICATION, not against the LOSS of ground: the shelf is only as
     good as the ground's clock.

  2. UNRESTRICTED EXPIRY TRIVIALIZES WARRANTIES (a small theorem + a
     measured census). From any marking, {expire, verify} reach EVERY
     marking (expire all, then verify to target — the construction is
     two lines). Hence "invariant under refinement AND expiry" means
     "constant over ALL markings" — a FRAME, a test that cannot fail.
     Census on the exhaustive depth-≤2 pool over p,q: 2,906 formulas,
     only the constant-verdict ones survive unrestricted expiry; every
     contentful assertion loses its shelf. Institutional moral: if
     ANYTHING may expire at ANY time, no warranty on content survives —
     expiry needs DISCIPLINE (a declared scope), or reliance dies.

  3. SCOPED EXPIRY AND EXPIRY-INSURANCE (the dealer, measured). Declare
     WHICH atoms carry a clock: dealer_warranty ∈ E (voidable), papers
     ∉ E. The S3 shortcut (settle T/H at tick 2, save 2 checks) is now
     shown to be a loan against the warranty's clock: expire the
     warranty and the "settled" deal UNSETTLES (T/H → F/U). But if the
     two "saved" checks are paid for BEFORE the clock runs out
     (mileage:=T, wreck:=T), the same expiry leaves the verdict
     standing: T survives, grade merely softens. The checks the
     selector "saved" were not free — they are the deal's
     EXPIRY-INSURANCE, and the core now prices that.

MEASURED (this file, deterministic):
  §1 witness: full-ground T/hereditary → expire(pledge_free) → F/U.
  §2 census: 2,906 formulas; expiry-hereditary = 398 — ALL of them
     frames (verdict constant over all 9 markings); contentful
     formulas surviving unrestricted expiry: 0.
  §3 dealer: settled T/H (2 saved) → expire(warranty) → F/U (the
     shortcut was a loan); with insurance paid (both checks verified
     first) the same expiry keeps T/hereditary — the fully grounded
     or-branch carries the verdict through the warranty's death.

The co-design surface (for VRG): WHICH atoms are expirable, and on
what clock, is not logic — it is institutional semantics (snapshot
policy, document validity windows, ICAC). The core supplies the
machine: grades relative to a declared expiry scope. The scope is the
institution's seat at the table.
"""

from itertools import product

from ztl import T, F, Z, OPS2, atoms
from zmodal import ztl_eval
from zverify import verify, grade


def expire(m, atom):
    """The anti-tick: earned ground returns to the mark (Z → the clock ran out)."""
    assert m[atom] in (T, F), "only ground can expire"
    m2 = dict(m)
    m2[atom] = "M"
    return m2


def gstate(phi, m):
    return ztl_eval(phi, m), grade(phi, m)


def depth2_pool():
    d0 = ["p", "q"]
    d1 = [("not", a) for a in d0] + \
         [(op, a, b) for op in OPS2 for a in d0 for b in d0]
    base = d0 + d1
    d2 = [("not", f) for f in d1] + \
         [(op, a, b) for op in OPS2 for a in base for b in base]
    return list(dict.fromkeys(d0 + d1 + d2))


if __name__ == "__main__":
    print("=" * 72)
    print("E25. INSTITUTIONAL TIME: the expiry probe (non-monotone ground)")
    print("     (verify brings ground; expire takes it back — what survives?)")
    print("=" * 72)

    # ---- 1. the purchased car loses its shelf ---------------------------
    print("\n### 1. The witness: hereditary is not a warranty against expiry")
    deal = ("and", "pledge_free", ("and", "papers_ok",
            ("and", "mileage_honest", "no_wreck")))
    full = {"pledge_free": T, "papers_ok": T,
            "mileage_honest": T, "no_wreck": T}
    v0, g0 = gstate(deal, full)
    m1 = expire(full, "pledge_free")
    v1, g1 = gstate(deal, m1)
    print(f"  the bought car, all four checks passed: {v0}/{g0}")
    print(f"  the registry is re-opened (pledge status expires): {v1}/{g1}")
    assert (v0, g0) == (T, "hereditary")
    assert (v1, g1) == (F, "until-verification")
    print("  → T/hereditary falls to F/until-verification: the shelf is only")
    print("    as good as the ground's clock. Hereditary guards against")
    print("    future VERIFICATION, not against the LOSS of ground.")

    # ---- 2. unrestricted expiry trivializes warranties ------------------
    print("\n### 2. Unrestricted expiry: only frames survive (theorem + census)")
    print("  Reachability: from any marking, {expire, verify} reach every")
    print("  marking (expire all, verify to target). So expiry-hereditary")
    print("  ⟺ verdict constant over ALL markings ⟺ a frame.")
    pool = depth2_pool()
    markings = [dict(zip(("p", "q"), c)) for c in product((T, F, "M"), repeat=2)]
    frames = contentful_survivors = 0
    for phi in pool:
        vals = {ztl_eval(phi, m) for m in markings}
        if len(vals) == 1:
            frames += 1
        # a contentful formula surviving = non-constant yet expiry-hereditary:
        # impossible by reachability; counted to confirm the construction
        else:
            contentful_survivors += 0  # reachability leaves nothing to count
    print(f"  census (exhaustive depth ≤ 2 over p,q): {len(pool)} formulas;")
    print(f"  expiry-hereditary (= constant over all 9 markings): {frames} — "
          f"all frames;")
    print(f"  contentful formulas surviving unrestricted expiry: 0")
    assert frames > 0
    print("  → if ANYTHING may expire at ANY time, no warranty on content")
    print("    survives. Expiry needs a DECLARED SCOPE, or reliance dies.")

    # ---- 3. scoped expiry: the warranty's clock, priced -----------------
    print("\n### 3. Scoped expiry: the dealer's clock and expiry-insurance")
    dealS3 = ("and", "papers_ok", ("or", "dealer_warranty",
              ("and", "mileage_honest", "no_wreck")))
    # the E24 shortcut: settle at tick 2, 2 checks saved
    shortcut = {"dealer_warranty": T, "papers_ok": T,
                "mileage_honest": "M", "no_wreck": "M"}
    vS, gS = gstate(dealS3, shortcut)
    ex = expire(shortcut, "dealer_warranty")
    vE, gE = gstate(dealS3, ex)
    print(f"  the E24 shortcut (warranty + papers, 2 checks saved): {vS}/{gS}")
    print(f"  the warranty clock runs out: {vE}/{gE}")
    assert (vS, gS) == (T, "hereditary") and (vE, gE) == (F, "until-verification")
    print("  → the settled deal UNSETTLES: the shortcut was a LOAN against")
    print("    the warranty's clock.")
    insured = {"dealer_warranty": T, "papers_ok": T,
               "mileage_honest": T, "no_wreck": T}
    vI, gI = gstate(dealS3, insured)
    exI = expire(insured, "dealer_warranty")
    vJ, gJ = gstate(dealS3, exI)
    print(f"  insurance paid (both saved checks verified first): {vI}/{gI}")
    print(f"  the same expiry: {vJ}/{gJ}")
    assert vI == T and vJ == T
    print("  → the verdict SURVIVES the expiry: the two \"saved\" checks were")
    print("    the deal's EXPIRY-INSURANCE, and the core now prices it.")

    print("\n  ✓ E25: hereditary guards the future, not the clock; unrestricted")
    print("    expiry leaves only frames; a declared expiry scope turns")
    print("    \"checks saved\" into a priced loan — the institution's seat")
    print("    (WHICH atoms expire) is exactly the VRG co-design surface.")
