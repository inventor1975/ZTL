# -*- coding: utf-8 -*-
"""
ztlnetwork — a mini-network of ZTL judge nodes, and a MEASURED stress test.

Not production consensus (that layer is adopted from mature BFT infra when a
real consortium exists). This composes the primitives we built — signed
attestations + proof-of-fault (ztljudgenode) — into a small network, and then
MEASURES two things instead of asserting them theoretically:

  A. Does it WORK, with real nodes and real signatures, at 4, 30, 90 judges?
     Honest nodes attest; a Byzantine minority forges lies; an auditor
     re-computes every attestation (proof-of-fault) and returns the verdict
     the honest set agrees on, flagging the liars.

  B. HOW MUCH more stable is it with more judges? Two different layers:
     - VERDICT layer: because every attestation is re-computable, liars are
       excluded no matter how many. The correct verdict survives even a
       supermajority of liars (shown directly).
     - INPUT / consensus layer: admitting which facts enter needs a Byzantine
       quorum, safe only while compromised ≤ f = ⌊(N−1)/3⌋. Here more judges
       DOES help — measured by Monte-Carlo: with a per-judge compromise
       probability p, P(network holds) = P(#compromised ≤ f). Concentration
       makes this sharpen dramatically as N grows — BELOW the 1/3 line. Above
       it, more judges only fail more certainly (you cannot out-number a real
       majority). The numbers show exactly that.

Run:  python3 ztlnetwork.py
"""
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ztljudgenode import Node, audit                                # noqa: E402
from ztl import T, F                                                # noqa: E402

CLAIM = "identity_check & funds_check"
ATOMS = [("identity_check", T, "verified", "gov"),
         ("funds_check", T, "cleared", "bank")]          # truth: T / EARNED


def bft_f(n: int) -> int:
    """Max Byzantine faults tolerated by the input/consensus layer: n ≥ 3f+1."""
    return (n - 1) // 3


def build(n: int):
    """n honest judge nodes sharing the same atom state (distinct signing ids)."""
    nodes = []
    for i in range(n):
        nd = Node(":memory:", seed=i.to_bytes(32, "big"))
        for name, v, reason, src in ATOMS:
            nd.assert_atom(name, v, reason, src)
        nodes.append(nd)
    return nodes


def network_verdict(attestations):
    """Audit every attestation (proof-of-fault) and return (verdict, faulty):
    the verdict the CONFIRMED honest nodes agree on, and the ids re-computation
    flagged as lying. Liars are excluded regardless of their count."""
    confirmed, faulty = {}, []
    for att in attestations:
        r = audit(att)
        if r["result"] == "CONFIRMED":
            confirmed[att["verdict"]] = confirmed.get(att["verdict"], 0) + 1
        else:
            faulty.append(att["node_id"][:12])
    verdict = max(confirmed, key=confirmed.get) if confirmed else None
    return verdict, faulty


def part_a():
    print("=" * 78)
    print("A. does it WORK at scale? real nodes, real Ed25519 signatures")
    print("=" * 78)
    print(f"\n{'judges':>7} {'f=liars tolerated':>18} {'verdict':>9} "
          f"{'liars flagged':>14}")
    print("-" * 78)
    for n in (4, 30, 90):
        nodes = build(n)
        f = bft_f(n)
        atts = [nodes[i].forge(CLAIM, F, "REFUTED") if i < f
                else nodes[i].attest(CLAIM) for i in range(n)]
        verdict, faulty = network_verdict(atts)
        ok = "T (correct)" if verdict == T else f"{verdict} (WRONG)"
        print(f"{n:>7} {f:>18} {ok:>9} {str(len(faulty) == f):>14}")
        assert verdict == T and len(faulty) == f

    # verdict layer robust to a SUPERMAJORITY of liars (proof-of-fault excludes)
    nodes = build(90)
    atts = [nodes[i].forge(CLAIM, F, "REFUTED") if i < 89
            else nodes[i].attest(CLAIM) for i in range(90)]      # 89 liars, 1 honest
    verdict, faulty = network_verdict(atts)
    print(f"\n  verdict layer: 89 of 90 lie, 1 honest → verdict "
          f"{'T (still correct)' if verdict == T else verdict}, "
          f"{len(faulty)} flagged")
    assert verdict == T and len(faulty) == 89


def part_b(trials=20000):
    print("\n" + "=" * 78)
    print("B. HOW MUCH more stable? input/consensus layer, Monte-Carlo "
          f"({trials} trials)")
    print("=" * 78)
    print("   P(network holds) = P(#compromised ≤ f), per-judge compromise "
          "probability p")
    print(f"\n   {'p':>6} │ {'N=4':>8} {'N=30':>8} {'N=90':>8}   note")
    print("   " + "-" * 60)
    notes = {0.10: "below 1/3 → more judges MUCH safer",
             0.20: "below 1/3 → concentration kicks in",
             0.34: "≈ the 1/3 line → sharp transition",
             0.50: "above 1/3 → more judges fail MORE surely"}
    for p in (0.10, 0.20, 0.34, 0.50):
        rates = []
        for n in (4, 30, 90):
            f = bft_f(n)
            holds = sum(
                1 for _ in range(trials)
                if sum(random.random() < p for _ in range(n)) <= f)
            rates.append(holds / trials)
        print(f"   {p:>6.2f} │ {rates[0]:>8.4f} {rates[1]:>8.4f} "
              f"{rates[2]:>8.4f}   {notes[p]}")


def main():
    part_a()
    part_b()
    print("\n" + "=" * 78)
    print("ZTLNETWORK GREEN — works with real nodes/signatures at 4/30/90; the")
    print("verdict layer survives any number of liars (proof-of-fault); the")
    print("consensus layer gets sharply more stable with more judges below the")
    print("1/3 line, and only more certainly broken above it. Measured, not")
    print("argued.")


if __name__ == "__main__":
    main()
