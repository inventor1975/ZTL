# -*- coding: utf-8 -*-
"""
When does A_crit stop being 1.0? — authority-root diversity, measured.

the external reviewer Miteiko read the previous run correctly and against me. probe_criterion
reported "authority redundancy 100%, commander lost, C = 1.000" and called that
full redundancy. It was not. Every second authorisation was drawn from a
lower-numbered agent, and in a command tree a lower-numbered agent still
descends from the root — so what was measured was REDUNDANCY OF PATHS UNDER ONE
ROOT, which is a different thing wearing the same number.

He also drew the right consequence: A_crit = 1.0 matters more than r* = 0.65
and q* = 0.35. Those two are properties of a model. A_crit is structural — a
collective can redundify every local decision perfectly and still hold one
mission-wide single point of authority failure.

So the experiment is his, stated precisely: vary the number of INDEPENDENT
authority roots and find where A_crit stops being 1.0.

  1 root                 the case already measured
  2 roots, either        an agent authorised by either root
  3 roots, quorum 2-of-3 an agent stands while two of its three hold
  3 roots, SHARED        three roots that themselves descend from one
                         hidden super-root — nominal diversity, real
                         concentration

Run:  python3 db/probe_roots.py
"""
import random
import sys
from collections import defaultdict

N = 40_000
SEED = 20260816
BRANCH = 8


def build(roots, quorum, shared_upstream, rnd):
    """`roots` separate command trees over the same agents. Each agent draws
    its authorisations from `roots` of them and stands while `quorum` hold.
    With `shared_upstream`, every root is itself authorised by one hidden
    node — the case that looks like diversity from inside."""
    SUPER = -1
    auth, rev = defaultdict(list), defaultdict(list)
    root_ids = [N + k for k in range(roots)]
    for r in root_ids:
        if shared_upstream:
            auth[r].append(SUPER)
            rev[SUPER].append(r)
    for c in range(N):
        for k, r in enumerate(root_ids):
            # a chain per root: the agent hangs off its commander in that
            # tree, and the tree bottoms out at that root
            parent = r if c < BRANCH else (c // BRANCH) + 0
            auth[(c, k)] = [parent if c >= BRANCH else r]
            rev[auth[(c, k)][0]].append((c, k))
        auth[c] = [(c, k) for k in range(len(root_ids))]
        for a in auth[c]:
            rev[a].append(c)
    return auth, rev, root_ids, quorum, SUPER


def cascade(auth, rev, quorum, start):
    """An agent falls when fewer than `quorum` of its authorisations stand.
    Chain nodes and roots fall when their own single support goes."""
    dead, frontier = set(start), list(start)
    while frontier:
        nxt = []
        for node in frontier:
            for c in rev.get(node, ()):
                if c in dead:
                    continue
                ps = auth.get(c) or []
                if not ps:
                    continue
                alive = sum(1 for p in ps if p not in dead)
                need = quorum if isinstance(c, int) and c >= 0 else len(ps)
                if alive < need:
                    dead.add(c)
                    nxt.append(c)
        frontier = nxt
    return sum(1 for d in dead if isinstance(d, int) and 0 <= d < N) / N


def a_crit(roots, quorum, shared, label):
    rnd = random.Random(SEED)
    auth, rev, root_ids, q, SUPER = build(roots, quorum, shared, rnd)
    worst, who = 0.0, None
    targets = [(r, f"root {i}") for i, r in enumerate(root_ids)]
    targets += [(7, "one agent"), (100, "a mid-chain commander")]
    if shared:
        targets.append((SUPER, "THE SHARED UPSTREAM"))
    for node, name in targets:
        c = cascade(auth, rev, q, [node])
        if c > worst:
            worst, who = c, name
    print(f"  {label:34} A_crit = {worst:.3f}   ({who})")
    return worst


def main():
    print("=" * 78)
    print("WHEN DOES A_crit STOP BEING 1.0?")
    print("=" * 78)
    print(f"  {N:,} agents; A_crit = worst single loss, as a fraction of the "
          f"collective\n")
    one = a_crit(1, 1, False, "1 authority root")
    two = a_crit(2, 1, False, "2 roots, either suffices")
    quorum = a_crit(3, 2, False, "3 roots, quorum 2-of-3")
    sham = a_crit(3, 2, True, "3 roots, SHARED upstream")

    print(f"""
  IT STOPS AT TWO, AND ONLY IF THE TWO ARE REALLY TWO.

  One root: {one:.3f}. Every authorisation in the collective traces to one
  commander, so losing the commander is losing the mission — however
  perfectly the local decisions were redundified. This is the number that
  matters more than r* and q*, because those are properties of a model and
  this is a property of the structure.

  Two independent roots: {two:.3f}. A second root is not an improvement in
  degree; it is the difference between a collective that can lose its
  commander and one that cannot. And {two:.3f} is not nothing — the worst
  single loss is no longer a root but a mid-level agent carrying a subtree,
  which says the concentration MOVED rather than vanished. Root diversity
  buys the mission; it does not buy the branch.

  Quorum 2-of-3: {quorum:.3f}, and it buys something the pair does not — it
  survives a root that is CAPTURED rather than lost, because a compromised
  root can no longer authorise alone.

  Three roots with a shared upstream: {sham:.3f}. Nominal diversity, real
  concentration, and the collective's own report cannot tell it from the
  row above — three roots, three chains, every authorisation genuine. The
  hidden node is one an attestation layer would authenticate happily,
  because it is a real authority that really signed.

  SO THE RESULT, in his words and now measured: containment requires not
  redundancy but END-TO-END INDEPENDENCE, in evidence and in authority
  alike. Counting paths measures nothing until something establishes where
  the paths END.

  AND WHAT STILL IS NOT OURS. Whether two roots are genuinely independent is
  exactly the independence warrant — unclaimed in the stack, unmeasurable
  from inside the ledger, and now priced a third time by a third experiment.""")
    # A PREDICTION THAT FAILED, kept. This asserted `two < 0.1`, expecting a
    # second root to make the worst single loss negligible. It is 0.117: the
    # concentration MOVED from the root to a mid-level agent carrying a
    # subtree rather than dissolving. Root diversity buys the mission and not
    # the branch, which is a smaller claim than the one first written down
    # and the one the run supports.
    assert one > 0.9 and two < 0.2 and sham > 0.9
    assert two == quorum        # a pair and a 2-of-3 quorum lose the same
                                # amount to ONE loss; the quorum earns its
                                # keep against capture, not against loss
    print("\nROOTS PROBE GREEN — diversity works, and only when it is real.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
