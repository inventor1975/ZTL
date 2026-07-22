# -*- coding: utf-8 -*-
"""
claim_ledger — ztljudge as a WARRANT JUDGE over a stream of dirty claims.

Not mathematics: everyday claims whose supporting facts are PARTLY checked.
Each claim is a small argument; the marking says which supporting facts are
verified (T), refuted (F), or still unchecked (Z, the default). The judge
sorts each claim by its warranty, not its bare truth, and names the weak link.

The point — the thing a plain truth-check and a proof kernel do NOT give:
    * two claims both read 'true', yet one is EARNED and one is ON CREDIT;
    * two claims both read 'not true', yet one is REFUTED and one is merely
      OPEN (not yet established) — one unchecked fact away from either answer.
Telling these apart, and pointing at the exact unverified link, is the sort.

Run:  python3 claim_ledger.py              (built-in stream)
      python3 claim_ledger.py claims.txt   (a stream from a file)
"""
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ztljudge import (judge, ledger, load_claims, next_check,       # noqa: E402
                     DISPOSITIONS)
from ztl import T                                                  # noqa: E402

# the built-in stream (used when no file is given)
CLAIMS = [
    ("both checks pass",          "identity & funds",   {"identity": T, "funds": T}),
    ("redundant unknown",         "approved | scratch", {"approved": T}),
    ("looks fine (double neg)",   "~~cleared",          {}),
    ("one check still pending",   "identity & funds",   {"identity": T}),
    ("revoked",                   "granted & ~revoked", {"granted": T, "revoked": T}),
]


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else None
    claims = load_claims(path) if path else CLAIMS
    src = path if path else "built-in stream"

    print("=" * 82)
    print(f"claim_ledger — ztljudge judges dirty claims by WARRANT, not truth  "
          f"[{src}]")
    print("=" * 82)
    result = ledger(claims)

    print(f"\n{'claim':26s} {'verdict':7s} {'grade':18s} disposition")
    print("-" * 82)
    for (_, text, mk), r in zip(claims, result["rows"]):
        print(f"{r['label']:26s} {r['verdict']:7s} {r['grade']:18s} "
              f"{r['disposition']}")
        print(f"    {r['formula']}   —   {r['why']}")
        if r["disposition"] in ("ON CREDIT", "OPEN"):
            nc = next_check(text, mk)
            if nc:
                tag = "settles either way" if nc["settles"] else "narrows it"
                print(f"      → check '{nc['atom']}' next:  T ⇒ {nc['if_T']}"
                      f",  F ⇒ {nc['if_F']}  ({tag})")

    print("\n" + "-" * 82)
    print("sorted by warranty:")
    for disp in DISPOSITIONS:
        labels = result["buckets"][disp]
        print(f"  {disp:10s} ({len(labels)}): {labels}")

    if not path:
        print("\nthe sort the verdict alone cannot make:")
        print("  · two T-claims, both EARNED — the judge knows the unknown does "
              "not matter.")
        print("  · 'looks fine' is also T, yet ON CREDIT: it rides an unverified "
              "link and dies if it flips.")
        print("  · two F-claims — one only OPEN (verify the link), one truly "
              "REFUTED.")
        # honest self-check on the built-in dispositions
        want = {"both checks pass": "EARNED", "redundant unknown": "EARNED",
                "looks fine (double neg)": "ON CREDIT",
                "one check still pending": "OPEN", "revoked": "REFUTED"}
        got = {r["label"]: r["disposition"] for r in result["rows"]}
        assert got == want, got
        print("\nCLAIM-LEDGER GREEN — earned / on-credit / open / refuted, each "
              "with its weak link named.")


if __name__ == "__main__":
    main()
