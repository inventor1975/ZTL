# -*- coding: utf-8 -*-
"""
zbook — the book of claims: what was asserted, what it rests on, and what
falls when a ground goes.

Stage 1 of the plan settled in words with the curator. The judge decides
one claim and forgets it; a mathematician uses proved theorems to prove
new ones. This is the first half of that: a ledger that KEEPS claims, so
that later stages can let one claim rest on another.

THE PRINCIPLE, and everything follows from it: the book does not store
verdicts as truth. It stores the claim and its grounds, and the verdict is
RECOMPUTED on every reading. A stored verdict would be exactly the sin
this corpus exists to refuse — a judgment taken on credit from a past
moment, when the ground may since have expired and the judge may since
have changed.

That last risk is not hypothetical here: the report shape changed six
times in two days of work. So the book carries a FINGERPRINT of the judge
— the verdicts it gives on a fixed battery of probe claims — and a
snapshot taken under a different fingerprint is flagged rather than
silently compared. The book can tell "the world changed" from "the judge
changed", which is the difference between a finding and an artefact.

Format: a claim is a sheet line, `id :: formula :: quantities`, so the
book is a claims sheet with a history. Witnesses live where they always
did, inside the quantities (`earned:inv-17`) — and in stage 2 they will be
allowed to name another claim.

Run:  python3 zbook.py
"""
import hashlib
import json
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from ztl import T, F, Z                                        # noqa: E402
from znumjudge import (judge_sheet_claim, parse_quantities,     # noqa: E402
                       load_sheet)

# A fixed battery. Its answers are the judge's signature: change how the
# floor decides anything here and the fingerprint moves, which is how a
# snapshot knows it is being compared against a different machine.
BATTERY = [
    ("b1", "a <= b", "a=1 earned:x, b=2 earned:y"),
    ("b2", "a <= b", "a=[0,10] credit, b=2 earned:y"),
    ("b3", "a == b", "a=1 earned:x, b=2 earned:y"),
    ("b4", "a == b", "a=8/3 earned:x, b=k, k=? int"),
    ("b5", "a == b", "a=1 earned:x m, b=1 earned:y RUB"),
    ("b6", "a <= b & ok", "a=1 earned:x, b=2 earned:y, ok=Z"),
]


def fingerprint():
    """A short hash of how the judge currently answers the battery."""
    parts = []
    for label, formula, data in BATTERY:
        try:
            q, m = parse_quantities(data)
            r = judge_sheet_claim(formula, q, m)
            parts.append(f"{label}:{r['disposition']}:{r.get('lazy')}")
        except Exception as exc:                    # a battery entry that
            parts.append(f"{label}:!{type(exc).__name__}")   # stops parsing
    return hashlib.sha256("|".join(parts).encode()).hexdigest()[:12]


def judge_book(claims):
    """Recompute every claim in the book. Nothing is read from a cache;
    the cache exists only to be compared with, never to answer from."""
    out = {}
    for claim_id, formula, data in claims:
        q, m = parse_quantities(data)
        r = judge_sheet_claim(formula, q, m)
        out[claim_id] = {
            "formula": formula,
            "disposition": r["disposition"],
            "lazy": r.get("lazy"),
            "next_check": r.get("next_check", []),
            "why": r.get("why"),
            "witnesses": sorted({v["witness"] for v in q.values()
                                 if v.get("witness")}),
        }
    return out


def snapshot(results):
    return {"judge": fingerprint(),
            "claims": {k: {"disposition": v["disposition"],
                           "lazy": v["lazy"]} for k, v in results.items()}}


def diff(old, new_results):
    """What moved since the snapshot — and whether the judge moved too."""
    new = snapshot(new_results)
    same_judge = old.get("judge") == new["judge"]
    changed, appeared, vanished = [], [], []
    for k, v in new["claims"].items():
        if k not in old.get("claims", {}):
            appeared.append(k)
        elif old["claims"][k] != v:
            changed.append((k, old["claims"][k], v))
    for k in old.get("claims", {}):
        if k not in new["claims"]:
            vanished.append(k)
    return {"same_judge": same_judge, "changed": changed,
            "appeared": appeared, "vanished": vanished,
            "old_judge": old.get("judge"), "new_judge": new["judge"]}


def census(results):
    by = {}
    for v in results.values():
        by[v["disposition"]] = by.get(v["disposition"], 0) + 1
    return by


# ================================================================ the bench
BOOK = [
    ("c1", "sum(line1,line2,line3) <= budget",
     "line1=1000 earned:inv-17, line2=2000 earned:inv-18, "
     "line3=1500 earned:inv-19, budget=5000 earned:order-o4"),
    ("c2", "total == 4500",
     "total=4500 earned:contract"),
    ("c3", "vat == total / 5",
     "vat=900 earned:inv-20, total=4500 earned:contract"),
    ("c4", "headcount < cap",
     "headcount=? credit int, cap=75 earned:law"),
    ("c5", "fee == area",
     "fee=5 earned:reg-7 RUB, area=3 earned:plan m2"),
]


def sec1_the_book_reads_itself():
    print("-" * 72)
    print("1. THE BOOK, RECOMPUTED FROM ITS GROUNDS")
    results = judge_book(BOOK)
    for cid, v in results.items():
        cure = f"  cure {v['next_check']}" if v["next_check"] else ""
        print(f"   {cid}  {v['disposition']:9} lazy={v['lazy']}{cure}")
    print(f"   census: {census(results)}")
    assert census(results)["EARNED"] == 3
    assert results["c4"]["disposition"] == "OPEN"
    assert results["c5"]["disposition"] == "E"
    print("   nothing here was read from a cache: every verdict was")
    print("   recomputed from the grounds as they stand now, which is the")
    print("   only way a book can be trusted after its world has moved.")
    return results


def sec2_the_judge_has_a_fingerprint(results):
    print("-" * 72)
    print("2. THE FINGERPRINT: telling a changed world from a changed judge")
    snap = snapshot(results)
    print(f"   judge fingerprint now: {snap['judge']}")
    d = diff(snap, results)
    print(f"   same book, same judge: changed={len(d['changed'])} "
          f"same_judge={d['same_judge']}")
    assert d["same_judge"] and not d["changed"]
    # the world moves: a witness is withdrawn from line3
    moved = [(cid, f, data.replace("line3=1500 earned:inv-19",
                                   "line3=1500 credit"))
             for cid, f, data in BOOK]
    d2 = diff(snap, judge_book(moved))
    print(f"   after inv-19 is withdrawn: changed={[c[0] for c in d2['changed']]}"
          f"  same_judge={d2['same_judge']}")
    assert [c[0] for c in d2["changed"]] == ["c1"]
    assert d2["same_judge"]
    print("   c1 moved and the judge did not — so this is news about the")
    print("   WORLD. Had the fingerprint differed, the same movement would")
    print("   have been news about the machine, and the book says which.")


def sec3_what_stage_one_does_not_do():
    print("-" * 72)
    print("3. WHAT THIS STAGE DOES NOT DO YET")
    print("   A witness is still an external name — `earned:inv-17`. Stage")
    print("   two lets it name another CLAIM, and then the book becomes a")
    print("   graph: warranty is inherited along citations (rest on a")
    print("   credit claim and yours cannot rise above it), retraction has")
    print("   a closure to compute, and a circular justification is caught")
    print("   by the passport we already own.")
    print("   Until then this is a ledger that recomputes itself honestly —")
    print("   which is little, and is the part everything else stands on.")


if __name__ == "__main__":
    print("=" * 72)
    print("ZBOOK — the book of claims, stage one")
    print("=" * 72)
    res = sec1_the_book_reads_itself()
    sec2_the_judge_has_a_fingerprint(res)
    sec3_what_stage_one_does_not_do()
    print("=" * 72)
    print("ZBOOK GREEN — the book stores claims and grounds and never a")
    print("verdict: every reading recomputes. A snapshot carries the")
    print("judge's fingerprint, so a moved verdict can be told from a moved")
    print("machine — news about the world, or news about us.")
