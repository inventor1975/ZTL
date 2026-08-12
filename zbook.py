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
did, inside the quantities — and one may now name another claim,
`earned:claim/c1`, which is the single change that turns the book into a
graph. Three things follow, none of them needing a new rule:

  * warranty is INHERITED. A citation is honoured exactly as far as the
    cited claim currently stands; cite anything short of EARNED and the
    quantity drops to credit;
  * retraction TRAVELS. Withdraw one invoice and the whole subtree moves,
    including claims that never named it — the auditor's question, "what
    falls if this is a lie", answered by name instead of by memory;
  * a CIRCLE of support is classified, not rejected. Mutual citation
    without negation is the truth-teller's shape, and the passport calls
    it UNDERDETERMINED: ungrounded rather than refuted, curable only by
    stipulating a member. Agrippa's second horn, mechanically.

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


CITE = "claim/"


def _cited(quantities):
    """The claims this one leans on: witnesses of the form claim/<id>."""
    return sorted({v["witness"][len(CITE):] for v in quantities.values()
                   if (v.get("witness") or "").startswith(CITE)})


def _order(book):
    """Dependency order, plus the cycles. A cycle is not an error here —
    it is a CIRCULAR JUSTIFICATION, which is a thing the corpus can
    classify rather than reject (Agrippa's second horn)."""
    deps, ids = {}, [c[0] for c in book]
    for cid, _f, data in book:
        q, _m = parse_quantities(data)
        deps[cid] = [d for d in _cited(q) if d in ids]
    order, seen, stack, cycles = [], set(), set(), []

    def visit(n, path):
        if n in seen:
            return
        if n in stack:                       # found a circle of support
            cycles.append(path[path.index(n):] + [n])
            return
        stack.add(n)
        for d in deps[n]:
            visit(d, path + [n])
        stack.discard(n)
        seen.add(n)
        order.append(n)

    for cid in ids:
        visit(cid, [])
    return order, deps, cycles


def judge_book(claims):
    """Recompute the whole book, in dependency order, resolving citations.

    A witness of the form `claim/<id>` is honoured only as far as that
    claim currently stands: cite an EARNED claim and the citation carries
    its weight; cite anything else and the quantity drops to credit. The
    inheritance needs no special rule — it is the ordinary refusal to take
    a ground on somebody else's word, applied to our own book."""
    book = list(claims)
    order, deps, cycles = _order(book)
    by_id = {cid: (f, data) for cid, f, data in book}
    in_cycle = {n for cyc in cycles for n in cyc}
    out = {}
    for cid in order:
        formula, data = by_id[cid]
        q, m = parse_quantities(data)
        cites = _cited(q)
        # resolve each citation against the claim it names
        weakened = []
        for name, qty_ in q.items():
            w = qty_.get("witness", "") or ""
            if not w.startswith(CITE):
                continue
            target = w[len(CITE):]
            stands = out.get(target, {}).get("disposition") == "EARNED"
            if not stands:
                qty_["prov"] = "credit"
                qty_["witness"] = None
                weakened.append((name, target))
        r = judge_sheet_claim(formula, q, m)
        out[cid] = {
            "formula": formula,
            "disposition": ("CIRCULAR" if cid in in_cycle
                            else r["disposition"]),
            "lazy": r.get("lazy"),
            "next_check": r.get("next_check", []),
            "why": r.get("why"),
            "cites": cites,
            "weakened_by": weakened,
            "witnesses": sorted({v["witness"] for v in q.values()
                                 if v.get("witness")}),
        }
    for cid, _f, _d in book:                 # cycles never reach `order`
        out.setdefault(cid, {"formula": by_id[cid][0],
                             "disposition": "CIRCULAR", "lazy": None,
                             "next_check": [], "why": "circular support",
                             "cites": deps[cid], "weakened_by": [],
                             "witnesses": []})
    return out


def classify_cycles(book):
    """A circle of support, handed to the instrument that already knows
    what to do with self-reference. Mutual citation with no negation is
    the truth-teller's shape, and the passport calls it what it is:
    UNDERDETERMINED — not refuted, ungrounded, and curable only by
    stipulating one of its members. That is Agrippa's second horn,
    classified rather than deplored."""
    from zpassport import passports
    _order_, deps, cycles = _order(list(book))
    out = []
    for cyc in cycles:
        members = sorted(set(cyc))
        system = {m: (deps[m][0] if deps[m] else m) for m in members}
        reports = passports(system)[1]
        kinds = sorted({k for _c, k, _w in reports}) or ["GROUNDED"]
        out.append((members, kinds))
    return out


def retract(book, witness):
    """A ground goes: the document is forged, or the certificate expired.
    Everything that named it drops to credit, and the book is recomputed —
    so the damage travels along citations by itself."""
    out = []
    for cid, formula, data in book:
        out.append((cid, formula,
                    data.replace(f"earned:{witness}", "credit")))
    return out


def fallout(book, witness):
    """What a retraction costs, claim by claim: (id, before, after)."""
    before, after = judge_book(book), judge_book(retract(book, witness))
    return [(cid, before[cid]["disposition"], after[cid]["disposition"])
            for cid in before
            if before[cid]["disposition"] != after[cid]["disposition"]]


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


CHAIN = [
    ("c1", "line == amount",
     "line=1500 earned:inv-19, amount=1500 earned:inv-19"),
    ("c2", "total == sum(a,b)",
     "total=4500 earned:claim/c1, a=3000 earned:inv-17, b=1500 earned:inv-18"),
    ("c3", "total <= budget",
     "total=4500 earned:claim/c2, budget=5000 earned:order-o4"),
]

CIRCLE = [
    ("a1", "x == y", "x=1 earned:claim/a2, y=1 earned:doc"),
    ("a2", "y == x", "y=1 earned:claim/a1, x=1 earned:doc"),
]


def sec3_a_claim_may_rest_on_a_claim():
    print("-" * 72)
    print("3. STAGE TWO: A WITNESS MAY NAME ANOTHER CLAIM")
    res = judge_book(CHAIN)
    for cid in ("c1", "c2", "c3"):
        v = res[cid]
        print(f"   {cid}  {v['disposition']:9} cites={v['cites']} "
              f"weakened_by={v['weakened_by']}")
    assert all(res[c]["disposition"] == "EARNED" for c in ("c1", "c2", "c3"))
    print("   a chain three deep, every link earned. And the inheritance is")
    print("   not a special rule: a citation is honoured exactly as far as")
    print("   the cited claim currently stands.")


def sec4_retraction_travels_by_itself():
    print("-" * 72)
    print("4. STAGE THREE: WHAT FALLS WHEN A GROUND GOES")
    hits = fallout(CHAIN, "inv-19")
    for cid, before, after in hits:
        print(f"   {cid}: {before} -> {after}")
    assert [h[0] for h in hits] == ["c1", "c2", "c3"]
    assert all(b == "EARNED" and a == "ON CREDIT" for _c, b, a in hits)
    print("   one invoice withdrawn and three claims move, two of them")
    print("   never naming it: the damage travelled along the citations by")
    print("   itself. This is the auditor's question — WHAT FALLS IF THIS")
    print("   IS A LIE — answered by name instead of by memory, and it is")
    print("   the reason the book stores grounds rather than verdicts.")


def sec5_a_circle_is_classified_not_rejected():
    print("-" * 72)
    print("5. STAGE FOUR: A CIRCLE OF SUPPORT, CLASSIFIED")
    res = judge_book(CIRCLE)
    print(f"   a1 {res['a1']['disposition']}, a2 {res['a2']['disposition']}")
    assert all(v["disposition"] == "CIRCULAR" for v in res.values())
    for members, kinds in classify_cycles(CIRCLE):
        print(f"   the circle {members}: passport {kinds}")
        assert kinds == ["UNDERDETERMINED"]
    print("   UNDERDETERMINED — not refuted, UNGROUNDED, and curable only")
    print("   by stipulating one member. That is Agrippa's circle, and the")
    print("   book reaches the verdict with the instrument it already had:")
    print("   mutual citation without negation is the truth-teller's shape.")


def sec6_what_is_still_missing():
    print("-" * 72)
    print("6. WHAT IS STILL MISSING")
    print("   Search. Nothing here finds the relevant stored claims for a")
    print("   new question — that is premise selection, a crowded field")
    print("   with strong tools (Sledgehammer and its kin), and this corpus")
    print("   would lose there. Citations are written by whoever writes the")
    print("   claim, and the machine only honours them honestly.")


if __name__ == "__main__":
    print("=" * 72)
    print("ZBOOK — the book of claims, stage one")
    print("=" * 72)
    res = sec1_the_book_reads_itself()
    sec2_the_judge_has_a_fingerprint(res)
    sec3_a_claim_may_rest_on_a_claim()
    sec4_retraction_travels_by_itself()
    sec5_a_circle_is_classified_not_rejected()
    sec6_what_is_still_missing()
    print("=" * 72)
    print("ZBOOK GREEN — the book stores claims and grounds and never a")
    print("verdict: every reading recomputes. A snapshot carries the")
    print("judge's fingerprint, so a moved verdict can be told from a moved")
    print("machine — news about the world, or news about us. A witness may")
    print("name another claim, and then warranty is inherited without a")
    print("special rule; withdraw one invoice and three claims move, two of")
    print("them never naming it; and a circle of support is classified")
    print("UNDERDETERMINED by the passport — Agrippa's second horn, cured")
    print("only by stipulating a member.")
