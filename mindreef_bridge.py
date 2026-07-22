# -*- coding: utf-8 -*-
"""
mindreef_bridge — run the ztljudge warrant judge over a live MindReef topic set.

MindReef (a discussion platform) marks each topic with a flat
`resolution_status` (open / discussing / resolved). Each topic collects IDEAS,
whose status is approved / rejected / pending. That maps cleanly onto ZTL:

    approved  →  T   (a grounded, accepted proposal)
    rejected  →  F   (a refuted proposal)
    pending   →  Z   (unverified — not yet adjudicated)

The warrant judge then reads each topic as the claim "this topic has a
standing accepted proposal" = OR over its ideas, and — separately — flags any
still-pending idea (a Z the flat status can silently ride over). The payoff is
the sort the status field cannot make: a topic marked `resolved` while ideas
are still pending is resolved ON PENDING, not earned; the judge names which
pending idea to resolve next.

Input: a JSON array of {id, title, resolution_status, ideas:[{id,status}]}
(pulled read-only from the MindReef DB; not committed — it is live user data).

Run:  python3 mindreef_bridge.py <topics.json>
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ztljudge import judge, next_check                             # noqa: E402
from ztl import T, F                                              # noqa: E402


def claim_of(topic):
    """The claim 'this topic has a standing accepted proposal', as an OR over
    its ideas, with the marking read from each idea's status."""
    atoms, marking = [], {}
    for idea in topic["ideas"]:
        a = f"idea{idea['id']}"
        atoms.append(a)
        if idea["status"] == "approved":
            marking[a] = T
        elif idea["status"] == "rejected":
            marking[a] = F
        # pending → leave unmarked → Z
    return " | ".join(atoms), marking


def pending_of(topic):
    return [i["id"] for i in topic["ideas"] if i["status"] == "pending"]


def main():
    if len(sys.argv) < 2:
        raise SystemExit("usage: python3 mindreef_bridge.py <topics.json>")
    topics = json.load(open(sys.argv[1], encoding="utf-8"))

    rows, riding = [], []
    tally = {}
    for t in topics:
        formula, marking = claim_of(t)
        r = judge(formula, marking)
        pend = pending_of(t)
        # composite MindReef reading
        if pend and r["disposition"] == "EARNED":
            disp = "ACCEPTED · rides pending"
        elif pend and r["disposition"] == "OPEN":
            disp = "OPEN · only pending"
        elif r["disposition"] == "EARNED":
            disp = "SETTLED"
        elif r["disposition"] == "REFUTED":
            disp = "ALL REJECTED"
        else:
            disp = r["disposition"]
        tally[disp] = tally.get(disp, 0) + 1
        rows.append((t, r, pend, disp))
        # the discrepancy: flat status says done, warrant says pending remain
        if pend and t["resolution_status"] in ("resolved", "discussing"):
            riding.append((t, pend))

    print("=" * 90)
    print(f"mindreef_bridge — warrant judge over {len(topics)} live topics "
          "with ideas")
    print("=" * 90)
    print(f"\n{'id':>4} {'MindReef':10s} {'a/r/p':7s} {'warrant disposition':22s} "
          "topic")
    print("-" * 90)
    for t, r, pend, disp in rows:
        a = sum(1 for i in t["ideas"] if i["status"] == "approved")
        rj = sum(1 for i in t["ideas"] if i["status"] == "rejected")
        counts = f"{a}/{rj}/{len(pend)}"
        print(f"{t['id']:>4} {t['resolution_status']:10s} {counts:7s} "
              f"{disp:22s} {t['title'][:34]}")

    print("\n" + "-" * 90)
    print("warrant tally:", tally)

    print("\n" + "=" * 90)
    print(f"DISCREPANCY — {len(riding)} topics MindReef calls resolved/"
          "discussing while ideas are still pending (status rides a Z):")
    print("=" * 90)
    for t, pend in riding:
        formula, marking = claim_of(t)
        nc = next_check(formula, marking)
        nxt = (f"resolve idea {nc['atom'].replace('idea','')} next"
               if nc else "—")
        print(f"  [{t['resolution_status']}] {t['id']} {t['title'][:44]}")
        print(f"       {len(pend)} pending: ideas {pend}  →  {nxt}")


if __name__ == "__main__":
    main()
