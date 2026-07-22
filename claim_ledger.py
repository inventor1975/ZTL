# -*- coding: utf-8 -*-
"""
claim_ledger — ztltool as a WARRANT JUDGE over dirty claims.

Not mathematics: everyday claims whose supporting facts are PARTLY checked.
Each claim is a small argument; the marking says which supporting facts are
verified (T), refuted (F), or still unchecked (Z, the default). The judge
sorts each claim by its warranty, not its bare truth, and names the weak link.

The point — the thing a plain truth-check and a proof kernel do NOT give:
    * two claims both read 'true', yet one is EARNED and one is ON CREDIT;
    * two claims both read 'not true', yet one is REFUTED and one is merely
      OPEN (not yet established) — one unchecked fact away from either answer.
Telling these apart, and pointing at the exact unverified link, is the sort.

Run:  python3 claim_ledger.py
"""
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ztltool import judge                                          # noqa: E402
from ztl import T, F                                               # noqa: E402

# label · claim (ztltool syntax) · marking (unlisted atoms are Z = unchecked)
CLAIMS = [
    ("both checks pass",
     "identity & funds",            {"identity": T, "funds": T}),
    ("redundant unknown",
     "approved | scratch",          {"approved": T}),            # scratch Z
    ("looks fine — double negative",
     "~~cleared",                   {}),                         # cleared Z
    ("one check still pending",
     "identity & funds",            {"identity": T}),            # funds Z
    ("revoked",
     "granted & ~revoked",          {"granted": T, "revoked": T}),
]


def main():
    print("=" * 78)
    print("claim_ledger — ztltool judges dirty claims by WARRANT, not truth")
    print("=" * 78)

    buckets = {"EARNED": [], "ON CREDIT": [], "OPEN": [], "REFUTED": []}
    print(f"\n{'claim':30s} {'verdict':7s} {'grade':18s} disposition")
    print("-" * 78)
    for label, text, mk in CLAIMS:
        r = judge(text, mk)
        buckets[r["disposition"]].append(label)
        print(f"{label:30s} {r['verdict']:7s} {r['grade']:18s} "
              f"{r['disposition']}")
        print(f"    {r['formula']}   —   {r['why']}")

    print("\n" + "-" * 78)
    print("sorted:")
    for disp in ("EARNED", "ON CREDIT", "OPEN", "REFUTED"):
        print(f"  {disp:10s}: {buckets[disp]}")

    print("\nthe sort the verdict alone cannot make:")
    print("  · 'both checks pass' and 'redundant unknown' both read T —")
    print("    but the judge EARNS both (the unknown simply does not matter).")
    print("  · 'looks fine' also reads T — yet it is ON CREDIT: it rides the")
    print("    unverified 'cleared', and dies if that turns false.")
    print("  · 'one check pending' and 'revoked' both read F — but one is only")
    print("    OPEN (verify 'funds') while the other is truly REFUTED.")

    # honest self-check on the dispositions
    assert judge("identity & funds", {"identity": T, "funds": T})["disposition"] == "EARNED"
    assert judge("approved | scratch", {"approved": T})["disposition"] == "EARNED"
    assert judge("~~cleared", {})["disposition"] == "ON CREDIT"
    assert judge("identity & funds", {"identity": T})["disposition"] == "OPEN"
    assert judge("granted & ~revoked", {"granted": T, "revoked": T})["disposition"] == "REFUTED"
    print("\nCLAIM-LEDGER GREEN — earned / on-credit / open / refuted, each with "
          "its weak link named.")


if __name__ == "__main__":
    main()
