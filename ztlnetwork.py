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
       quorum, safe only while compromised ≤ f = ⌊(N−1)/3⌋. With a per-judge
       compromise probability p, P(network holds) = P(#compromised ≤ f) — and
       that number depends on HOW the compromises are joined, which p does not
       say. CORRECTED 2026-11-05 (found reviewing the probability work under
       ZTL degrees): this section used to report only the INDEPENDENT case (a
       Monte-Carlo of independent draws) and concluded "more judges are much
       safer below the 1/3 line". Independence was never declared. Now both:
         * the joint UNKNOWN (ZTL's default: any joint keeping each judge's p):
           P(holds) ≥ 1 − N·p/(f+1), exactly — Markov's bound, ATTAINED by the
           joint that puts mass N·p/(f+1) on "exactly f+1 compromised" (spread
           over all such sets) and the rest on "none". It does NOT improve with
           N (0.80 at N=4, 0.70 at N=30 and N=90 for p = 1/10): one shared bug,
           one vendor, one key-management slip — correlated compromise — and
           more judges buy nothing;
         * independence STIPULATED: the binomial, computed exactly; there, and
           only there, concentration makes more judges much safer below 1/3.
       The lever the numbers point at is the independence of the judges'
       failure domains, not their count — and that is a premise to establish
       (diverse code, operators, keys), never a default.

Run:  python3 ztlnetwork.py
"""
import os
from fractions import Fraction
from math import comb
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


def holds_unknown_joint(n, p):
    """[lo, hi] of P(#compromised <= f) over EVERY joint keeping each judge's marginal p — exact (Fractions). The
    objective and the constraints are symmetric in the judges, so averaging any joint over the permutations keeps
    both: an optimum is exchangeable, i.e. a distribution q_0..q_n of the COUNT with sum q_k = 1 and
    sum k q_k = n p. That small LP is solved by zdegree's exact simplex (ends certified there)."""
    import zdegree
    f = bft_f(n)
    good = [Fraction(1) if k <= f else Fraction(0) for k in range(n + 1)]
    rows = [([Fraction(1)] * (n + 1), "=", Fraction(1)),
            ([Fraction(k) for k in range(n + 1)], "=", n * p)]
    hi, _x = zdegree.lp_max(good, rows)
    neg, _y = zdegree.lp_max([-g for g in good], rows)
    return -neg, hi


def holds_independent(n, p):
    """P(#compromised <= f) when the judges' compromises are INDEPENDENT (a stipulation) — exact binomial."""
    f = bft_f(n)
    return sum(comb(n, k) * p ** k * (1 - p) ** (n - k) for k in range(f + 1))


def part_b():
    print("\n" + "=" * 78)
    print("B. HOW MUCH more stable? input/consensus layer (corrected 2026-11-05)")
    print("=" * 78)
    print("   P(network holds) = P(#compromised ≤ f), per-judge compromise probability p;")
    print("   the joint of the compromises UNKNOWN (lower end) vs independence STIPULATED")
    print(f"\n   {'p':>6} │ {'joint unknown: lower end':^28} │ {'independent (stipulated)':^28}")
    print(f"   {'':>6} │ {'N=4':>8} {'N=30':>9} {'N=90':>9} │ {'N=4':>8} {'N=30':>9} {'N=90':>9}")
    print("   " + "-" * 72)
    table = {}
    for p in (Fraction(1, 10), Fraction(1, 5), Fraction(17, 50), Fraction(1, 2)):
        lo = [holds_unknown_joint(n, p)[0] for n in (4, 30, 90)]
        ind = [holds_independent(n, p) for n in (4, 30, 90)]
        table[p] = (lo, ind)
        print(f"   {float(p):>6.2f} │ " + " ".join(f"{float(x):>8.4f}" for x in lo[:1]) +
              " " + " ".join(f"{float(x):>9.4f}" for x in lo[1:]) + " │ " +
              " ".join(f"{float(x):>8.4f}" for x in ind[:1]) + " " + " ".join(f"{float(x):>9.4f}" for x in ind[1:]))
    # the lower end is Markov's bound 1 - N p / (f+1), clipped at 0 — checked against the LP for every cell
    for p, (lo, _ind) in table.items():
        for n, v in zip((4, 30, 90), lo):
            assert v == max(Fraction(0), 1 - n * p / (bft_f(n) + 1)), (p, n, v)
    # ... and ATTAINED: mass N p/(f+1) on every (f+1)-set alike, the rest on 'none' — each judge's marginal is p
    from itertools import combinations
    n, p = 4, Fraction(1, 10)
    f = bft_f(n)
    sets = list(combinations(range(n), f + 1))
    w = n * p / (f + 1) / len(sets)
    assert all(sum(w for s_ in sets if j in s_) == p for j in range(n))
    assert 1 - w * len(sets) == table[p][0][0]
    # ... and the full-joint LP over the 16 worlds (no symmetry assumed) agrees at N = 4
    import zdegree
    c = [f"c{i}" for i in range(n)]
    terms = ["(" + " & ".join("~" + x for x in c) + ")"] + \
            ["(" + " & ".join(x if j == i else "~" + x for j, x in enumerate(c)) + ")" for i in range(n)]
    full = zdegree.degree(" | ".join(terms), {x: (p, p) for x in c})
    assert (full["lo"], full["hi"]) == holds_unknown_joint(n, p)
    # both sides: under independence more judges DO help below 1/3; with the joint unknown they do not
    lo10, ind10 = table[Fraction(1, 10)]
    assert ind10[0] < ind10[1] < ind10[2] and lo10[2] <= lo10[0]
    print("\n   joint unknown: 1 − N·p/(f+1), attained (checked: the LP, an explicit joint, and the full 16-world")
    print("   LP at N=4). More judges do NOT raise it — correlated compromise is not out-numbered. Only with")
    print("   independence STIPULATED does concentration make more judges much safer below 1/3. The premise to")
    print("   establish is the independence of failure domains, not the number of judges.")


def main():
    part_a()
    part_b()
    print("\n" + "=" * 78)
    print("ZTLNETWORK GREEN — works with real nodes/signatures at 4/30/90; the")
    print("verdict layer survives any number of liars (proof-of-fault); the")
    print("consensus layer gets more stable with more judges ONLY if their")
    print("compromises are independent — a premise to establish; with the joint")
    print("unknown its guarantee is 1 - N p/(f+1) and does not grow with N.")


if __name__ == "__main__":
    main()
