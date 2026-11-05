# -*- coding: utf-8 -*-
"""
zswarm_bounds — how loose is the proved capture bound for the tree of triples, and what do random seats buy?
(2026-11-05, the curator: "оба результата — в Lean ... плюс замер грубости второй границы на симуляции. Делай".)

THE TREE (lean/ZMajority.lean): 3^d seats, each triple decided 2-of-3, up to one verdict. A seat lies (F) or is
honest (T). `ZSwarmBounds.tree_bound` proves, for EVERY joint of the liars: P(the tree says F) <= E[lies] / 2^d,
i.e. <= 3^d p / 2^d when each seat lies with probability p. Three regimes, computed EXACTLY here (Fractions):

  (a) FIXED SEATS, the liars' joint unknown: the bound 3^d p / 2^d is ATTAINED — mix the capture configurations
      (2^d liars placed right, `ZMajority.capture`) over the tree's symmetries, so every seat lies with
      probability p and the tree is captured with probability 3^d p / 2^d (as long as that is <= 1);
  (b) SEATS DRAWN AT RANDOM (public randomness, OURS, so its independence of the liars is earned by construction),
      the liars' joint still unknown: given k liars, the tree sees a uniformly random k-set of seats; with c(k)
      the share of k-sets that capture (exact count by dynamic programming over the tree), the worst case over
      every distribution of k with mean 3^d p is the concave envelope of c at 3^d p — a two-point LP;
  (c) independence of the liars STIPULATED: q_{j+1} = 3 q_j^2 - 2 q_j^3 from q_0 = p.
MEASURED HERE: c(k) by DP is checked against brute force over all 512 liar sets of the 9-seat tree; (a) >= (b) >= (c)
in every row; (a) is attained by an explicit symmetric mixture (each seat's marginal checked to be p).

WHAT IT SAYS: the proved bound is the truth for FIXED seats — an adversary who knows the seats and correlates its
liars gets exactly it. Random seats are what make it loose; how much they buy, with the liars' correlation still
unknown, is column (b). Independence of the liars (column c) is a premise about the world and is never assumed.

Run:  python3 zswarm_bounds.py
"""
from fractions import Fraction as Fr
from itertools import combinations
from math import comb


def capture_counts(d):
    """-> list cap[k] = number of k-subsets of the 3^d seats whose lies make the tree say F (no empty seats)."""
    # dp[j] maps number_of_liars -> (count of sets giving F, count giving T) for a subtree of depth j
    dp = {0: (0, 1), 1: (1, 0)}                                 # a leaf: honest -> T, liar -> F
    for _ in range(d):
        nxt = {}
        for ka, (fa, ta) in dp.items():
            for kb, (fb, tb) in dp.items():
                for kc, (fc, tc) in dp.items():
                    k = ka + kb + kc
                    # 2-of-3: F iff at least two children say F
                    f_ = fa * fb * fc + fa * fb * tc + fa * tb * fc + ta * fb * fc
                    t_ = ta * tb * tc + fa * tb * tc + ta * fb * tc + ta * tb * fc
                    pf, pt = nxt.get(k, (0, 0))
                    nxt[k] = (pf + f_, pt + t_)
        dp = nxt
    n = 3 ** d
    return [dp.get(k, (0, 0))[0] for k in range(n + 1)]


def brute_counts_depth2():
    """the same count by brute force for the 9-seat tree"""
    def fold(bits):
        trip = [sum(bits[3 * i:3 * i + 3]) >= 2 for i in range(3)]
        return sum(trip) >= 2
    out = [0] * 10
    for k in range(10):
        for s in combinations(range(9), k):
            bits = [1 if i in s else 0 for i in range(9)]
            out[k] += fold(bits)
    return out


def envelope(c, mean):
    """max of sum_k P(k) c(k) over distributions of k on 0..n with the given mean — at most two support points"""
    n = len(c) - 1
    best = Fr(0)
    for k1 in range(n + 1):
        for k2 in range(k1, n + 1):
            if k1 <= mean <= k2:
                if k1 == k2:
                    v = c[k1]
                else:
                    w2 = (mean - k1) / (k2 - k1)
                    v = (1 - w2) * c[k1] + w2 * c[k2]
                best = max(best, v)
    return best


def independent(p, d):
    q = p
    for _ in range(d):
        q = 3 * q * q - 2 * q * q * q
    return q


if __name__ == "__main__":
    assert capture_counts(2) == brute_counts_depth2(), (capture_counts(2), brute_counts_depth2())
    print("-" * 72)
    print("1. c(k) BY DYNAMIC PROGRAMMING = BRUTE FORCE on the 9-seat tree (all 512 liar sets)")
    d = 4
    n = 3 ** d
    cap = capture_counts(d)
    c = [Fr(cap[k], comb(n, k)) for k in range(n + 1)]
    assert c[2 ** d - 1] == 0 and c[2 ** d] > 0 and c[n] == 1          # 16 liars are needed, and can suffice
    print(f"   depth {d}: {n} seats; no k-set with k < {2 ** d} captures; at k = {2 ** d} the share is "
          f"{cap[2 ** d]}/{comb(n, 2 ** d)} = {float(c[2 ** d]):.3e}")
    print("-" * 72)
    print("2. P(CAPTURE), 81 SEATS: (a) fixed seats, joint unknown = the PROVED bound, attained;")
    print("   (b) random seats, joint unknown; (c) liars independent (stipulated)")
    print(f"   {'p':>6} │ {'(a) 81p/16':>12} {'(b) random seats':>17} {'(c) independent':>16}")
    rows = []
    for p in (Fr(1, 100), Fr(1, 20), Fr(1, 10), Fr(1, 5), Fr(3, 10)):
        a = min(Fr(1), n * p / 2 ** d)
        b = envelope(c, n * p)
        ci = independent(p, d)
        assert a >= b >= ci, (p, a, b, ci)
        rows.append((p, a, b, ci))
        print(f"   {float(p):>6.2f} │ {float(a):>12.4f} {float(b):>17.4f} {float(ci):>16.2e}")
    # (a) attained: the symmetric mixture of capture configurations gives every seat marginal p
    # capture configurations: choose 2 of 3 children at every node, recursively; their number and seat coverage
    def configs(depth):
        if depth == 0:
            return [frozenset([0])]
        sub = configs(depth - 1)
        size = 3 ** (depth - 1)
        out = []
        for pair in ((0, 1), (0, 2), (1, 2)):
            for s1 in sub:
                for s2 in sub:
                    out.append(frozenset({pair[0] * size + x for x in s1} | {pair[1] * size + x for x in s2}))
        return out
    cf = configs(3)                                             # depth 3 (27 seats) keeps this enumeration small
    seats3, need3 = 27, 8
    cover = [sum(1 for s in cf if i in s) for i in range(seats3)]
    assert len(set(cover)) == 1 and all(len(s) == need3 for s in cf)
    p = Fr(1, 10)
    mass = seats3 * p / need3                                   # mixture weight on capture, spread evenly over cf
    marginal = mass * Fr(cover[0], len(cf))
    assert marginal == p
    print(f"\n   (a) is attained (checked at depth 3, 27 seats): the {len(cf)} capture configurations cover every")
    print(f"   seat equally ({cover[0]} each), so spreading weight {mass} over them gives every seat probability")
    print(f"   {marginal} and the tree is captured with probability {mass} = 27p/8 — the bound, exactly.")
    p10 = [r for r in rows if r[0] == Fr(1, 10)][0]
    print("-" * 72)
    print(f"SWARM BOUNDS GREEN — at p = 0.1, 81 seats: fixed seats {float(p10[1]):.4f} (proved, attained),")
    print(f"random seats {float(p10[2]):.4f} with the liars' joint unknown, {float(p10[3]):.1e} only if they are independent.")
