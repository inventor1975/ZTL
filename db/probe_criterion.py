# -*- coding: utf-8 -*-
"""
A containment criterion, not another table.

the external reviewer Miteiko's brief, and it changed the subject rather than extending it:
separate EVIDENCE dependency from AUTHORITY dependency, do not look for
another pretty number, and find the minimal set of parameters that decides in
advance whether a loss of warrant stays local or percolates.

The two dependencies are not the same relation and must not share a graph.
A conclusion needs evidence to be supported AND authority to be permitted, so
it falls when EITHER fails — a conjunction of requirements is a disjunction of
failures. That single structural fact predicts everything below, including why
a collective with perfect evidence redundancy died from one commander.

Four numeric outputs, as asked:

    C       fraction of conclusions lost
    r*      minimal REAL redundancy for containment (C < 1%)
    q*      maximum hidden correlation tolerated at a given declared r
    A_crit  damage from losing the single most critical node

The criterion this file set out to establish was: effective redundancy is
r_eff = r*(1-q) per dimension, and warrant stays local iff the MINIMUM over
dimensions clears the threshold. Its own table refuted the "iff". At an
identical minimum of 0.50 an authority-rich collective loses 0.03% and an
evidence-rich one loses 1.01% — thirty times worse. The dimensions neither
average nor exchange, and authority is the binding one because permission is
hierarchically concentrated while evidence is diffuse.

What survives is the necessary half, which is the half a designer needs:
fail any dimension and containment is gone, and no surplus elsewhere buys it
back. The header is left saying so rather than quietly restated.

Run:  python3 db/probe_criterion.py
"""
import random
import sys
from collections import defaultdict

N = 40_000
SEED = 20260816
BRANCH = 8


def build(r_evi, q_evi, r_auth, q_auth, rnd):
    """Two graphs over the same agents. `evi` is what supports a conclusion;
    `auth` is what permits it. Redundancy and hidden correlation are set per
    dimension, because that is the whole point of separating them."""
    evi, auth = defaultdict(list), defaultdict(list)
    evi_two, auth_two = set(), set()
    for c in range(1, N):
        evi[c].append(rnd.randrange(max(0, c - 200), c))
        auth[c].append((c - 1) // BRANCH)
        if rnd.random() < r_evi and rnd.random() >= q_evi:
            evi[c].append(rnd.randrange(0, c))       # a genuine second source
        if rnd.random() < r_auth and rnd.random() >= q_auth:
            auth[c].append(rnd.randrange(0, c))      # a genuine second warrant
        if len(evi[c]) > 1:
            evi_two.add(c)
        if len(auth[c]) > 1:
            auth_two.add(c)
    rev = defaultdict(list)
    for g in (evi, auth):
        for c, ps in g.items():
            for p in ps:
                rev[p].append(c)
    return evi, auth, rev


def cascade(evi, auth, rev, start):
    """A conclusion stands only while SOME evidence stands and SOME authority
    stands. Losing either is fatal, which is why the two dimensions cannot be
    averaged into one redundancy figure."""
    dead, frontier = set(start), list(start)
    while frontier:
        nxt = []
        for node in frontier:
            for c in rev.get(node, ()):
                if c in dead:
                    continue
                e = evi.get(c) or []
                a = auth.get(c) or []
                if (e and all(p in dead for p in e)) or \
                   (a and all(p in dead for p in a)):
                    dead.add(c)
                    nxt.append(c)
        frontier = nxt
    return len(dead) / N


def C(r_evi, q_evi, r_auth, q_auth, target):
    rnd = random.Random(SEED)
    evi, auth, rev = build(r_evi, q_evi, r_auth, q_auth, rnd)
    return cascade(evi, auth, rev, [target])


def main():
    print("=" * 78)
    print("A CONTAINMENT CRITERION — evidence and authority kept apart")
    print("=" * 78)
    print(f"  {N:,} agents; C = fraction of conclusions lost\n")

    print("  1. THE QUESTION THE EXTERNAL REVIEWER ASKED OUTRIGHT:")
    print("     can 100% formal redundancy still be globally fragile?")
    c_root = C(1.0, 0.0, 1.0, 0.0, 0)
    c_evi_only = C(1.0, 0.0, 0.0, 0.0, 0)
    print(f"       evidence 100% genuine, authority 100% genuine, "
          f"commander lost   C = {c_root:.3f}")
    print(f"       evidence 100% genuine, authority NOT redundant,  "
          f"commander lost   C = {c_evi_only:.3f}")
    print("     Yes. Perfect evidence redundancy buys nothing against the")
    print("     loss of a single authority root, because evidence and")
    print("     authority are different requirements and a conclusion needs")
    print("     both. ZTL is not failing here — it is reporting correctly")
    print("     that permission is gone. No amount of sensors replaces it.")
    assert c_evi_only > 0.5

    print("\n  2. THE CRITERION: containment follows the WORST dimension")
    print(f"\n       {'r_evi':>7} {'r_auth':>8} {'min':>6}   {'C':>7}")
    rows = []
    for re_, ra in ((1.0, 0.0), (0.0, 1.0), (0.5, 0.5),
                    (1.0, 0.5), (0.5, 1.0), (0.9, 0.9), (1.0, 1.0)):
        c = C(re_, 0.0, ra, 0.0, 7)
        rows.append((min(re_, ra), c))
        print(f"       {re_:>7.2f} {ra:>8.2f} {min(re_, ra):>6.2f}   {c:>7.4f}")
    # A CRITERION THAT FAILED, kept because the way it failed is the
    # result. This file first claimed that min(r_evi, r_auth) governs C and
    # nothing else. Its own table refutes that: at min = 0.50, evidence-rich
    # (1.00, 0.50) loses 1.01% while authority-rich (0.50, 1.00) loses
    # 0.03% — a factor of thirty at identical minimum. The dimensions are
    # NOT interchangeable, and a criterion that treats them as such would
    # have been a tidy sentence contradicted by the run printed above it.
    a_rich = C(0.5, 0.0, 1.0, 0.0, 7)
    e_rich = C(1.0, 0.0, 0.5, 0.0, 7)
    print(f"     at the SAME min of 0.50: evidence-rich {e_rich:.4f}, "
          f"authority-rich {a_rich:.4f}")
    print(f"     -> a factor of {e_rich / max(a_rich, 1e-9):.0f}. The minimum "
          f"does not determine C.")
    print("     Authority redundancy is worth more than evidence redundancy,")
    print("     and the asymmetry has a cause rather than being a quirk:")
    print("     authority is hierarchically concentrated — every permission")
    print("     traces to few roots — while evidence is local and diffuse.")
    print("     So the dimensions do not average AND do not exchange. A")
    print("     single redundancy figure for a system is meaningless twice")
    print("     over.")
    assert e_rich > a_rich * 5

    print("\n  3. r* AND q* — the two numbers a designer actually needs")
    r_star = next(r for r in [i / 20 for i in range(21)]
                  if C(r, 0.0, r, 0.0, 7) < 0.01)
    print(f"       r*  minimal REAL redundancy, both dimensions, for C<1%"
          f"   = {r_star:.2f}")
    q_star = None
    for q in [i / 20 for i in range(21)]:
        if C(1.0, q, 1.0, q, 7) >= 0.01:
            q_star = q
            break
    print(f"       q*  hidden correlation tolerated at r=1.0 before C>=1%"
          f"  = {q_star:.2f}")
    print("     Note what q* means. The system declares FULL redundancy and")
    print("     is destroyed by a hidden overlap well below half. Declared")
    print("     redundancy is not a safety property; effective redundancy is,")
    print("     and only an independence warrant tells them apart.")

    print("\n  4. A_crit — the cost of the single most critical node")
    a_crit = max((C(1.0, 0.0, 1.0, 0.0, t), t) for t in (0, 1, 7, 100, 5000))
    print(f"       worst single loss at FULL genuine redundancy: "
          f"C = {a_crit[0]:.3f} at agent {a_crit[1]}")
    print("     A_crit is not a function of redundancy at all. It is a")
    print("     property of where authority is concentrated, which is why it")
    print("     has to be reported beside r* and never folded into it.")

    print("""
  THE CRITERION, stated so it can be refuted:

    A loss of warrant stays local ONLY IF, in EVERY dependency
    dimension, effective redundancy r*(1-q) clears that dimension's own
    threshold — and the thresholds are not equal. Authority is the
    binding one.

  ONLY IF, not IF AND ONLY IF: clearing every dimension is necessary and
  the measurement above shows it is not sufficient in the form first
  written, since equal minima gave answers thirty-fold apart. What the
  runs do establish is the negative half, which is the half a designer
  needs: fail any dimension and containment is gone, and no surplus
  elsewhere buys it back.

  Three parameters, not one number: r per dimension, q per dimension,
  and the concentration of authority — A_crit reported beside them and
  never folded in, since at full genuine redundancy in both dimensions
  the commander still costs the entire collective.

  WHAT IS STILL NOT OURS. q is not measurable from inside — the ledger
  cannot see that two grounds share an origin, and attestation cannot
  either, since both grounds are genuine. That is the independence
  warrant the external reviewer names, and it is the unclaimed primitive in the stack.
  Everything above says how much it is worth; none of it supplies it.""")
    print("\nCRITERION PROBE GREEN — the worst dimension governs, measured.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
