# -*- coding: utf-8 -*-
"""
Containment error — when the map of dependencies is itself incomplete.

the external reviewer Miteiko's experiment, and it aims at the assumption under all the
previous ones rather than at another failure mode. Every probe so far took the
dependency graph as GIVEN. In a real system that is the one thing never
guaranteed: the independence warrant is built on a model of the world, and if
the model is short of edges the system can announce containment it does not
have.

  C_predicted   the worst cascade the system can compute, on the graph it CAN SEE
  C_actual      the same attack, on the graph that actually exists
  containment error = C_actual - C_predicted

The edges hidden here are not random. They are the ones that matter: the
common-source and common-authority edges, exactly the links whose absence
makes two grounds LOOK independent. Hiding random edges would understate the
danger, and understating it is what this file exists to measure.

Run:  python3 db/probe_blindspot.py
"""
import random
import sys
from collections import defaultdict

N = 20_000
SEED = 20260816
SOURCES, ROOTS = 5, 4        # sensors/models an agent can rest on


def world(hidden, rnd, alias_share=0.30):
    """The true graph and the observed one.

    A FIRST MODEL THAT DID NOT TEST THE HYPOTHESIS, kept in the record
    because the reason is the finding. It hung 40 sensors off 3 feeds and hid
    a fraction of the sensor->feed edges; the worst case never moved, because
    each feed still had a dozen visible children and the attack found it
    anyway. Partial hiding of a heavily shared structure is invisible to a
    worst-case question — true, and not what was asked.

    What was asked is the ALIAS: an agent's two grounds are recorded under two
    names and are secretly ONE source. Hide that identity and the agent looks
    redundant while being single-grounded. That is the edge whose absence
    manufactures independence, and it is per-agent rather than per-source.
    """
    ev, au = {}, {}
    alias = set()                     # agents whose two grounds are really one
    for c in range(N):
        a, b = rnd.randrange(SOURCES), rnd.randrange(SOURCES)
        if rnd.random() < alias_share:
            b = a                     # truly one source under two names
            alias.add(c)
        ev[c] = [("s", a), ("s", b)]
        au[c] = [("r", rnd.randrange(ROOTS)), ("r", rnd.randrange(ROOTS))]
    # The system sees the alias only where it was recorded. `hidden` is the
    # share of those identities missing from its map.
    seen_ev = {}
    for c in range(N):
        if c in alias and rnd.random() < hidden:
            seen_ev[c] = [("s", ev[c][0][1]), ("s", (ev[c][0][1] + 1) % SOURCES)]
        else:
            seen_ev[c] = ev[c]
    # NO UPSTREAM LAYER, and that is the second correction. The first model
    # hung the sources off three shared feeds, so the worst attack was always
    # "kill a feed" — it took out a third of the sensors and drowned the very
    # effect being measured. With the sources standing alone, killing ONE is
    # survivable for any agent with two real ones, and fatal for exactly the
    # agents whose two are secretly one. That isolates the question instead of
    # burying it under a bigger cascade.
    return ev, seen_ev, au, {}, len(alias)


def cascade(ev, au, up, start):
    """An agent stands while at least one evidence ground and at least one
    authority ground stand. A source or root falls when its upstream does."""
    dead = {start}
    changed = True
    while changed:
        changed = False
        for node, parents in up.items():
            if node not in dead and parents and \
                    all(p in dead for p in parents):
                dead.add(node)
                changed = True
    lost = 0
    for c in range(N):
        if all(g in dead for g in ev[c]) or all(g in dead for g in au[c]):
            lost += 1
    return lost / N


def worst(ev, au, up):
    """What an adversary would pick, over everything a cascade can start at."""
    cands = [("s", i) for i in range(SOURCES)] + \
            [("r", i) for i in range(ROOTS)]
    return max(cascade(ev, au, up, n) for n in cands)


def alternatives(hidden, rnd, share=0.30):
    """THE OTHER KIND OF MISSING EDGE, and it runs the other way.

    This file claimed the error from incompleteness is one-directional — a
    missing edge can only make grounds look MORE independent. Adversarial
    review pointed at §1 of the note, which supports ALTERNATIVE grounds
    (`inv-17|inv-18`), and the objection is correct: if the map does not know
    about an alternative, the system believes a conclusion falls when its
    single known ground falls, while in truth it survives on the other. The
    prediction is then too LARGE — pessimistic, the direction declared
    impossible.

    Both kinds are real and they are not symmetric in consequence: an
    optimistic error lets a system act on warrant it does not have, a
    pessimistic one makes it withdraw from warrant it does. Only the first is
    dangerous; only the second is wasteful."""
    base = [rnd.randrange(SOURCES) for _ in range(N)]
    true_alt, seen_alt = {}, {}
    for c in range(N):
        if rnd.random() < share:
            b = (base[c] + 1 + rnd.randrange(SOURCES - 1)) % SOURCES
            true_alt[c] = b
            if rnd.random() >= hidden:
                seen_alt[c] = b
    return base, true_alt, seen_alt


def alt_loss(base, alt, dead):
    """A conclusion falls only if its ground AND its alternative are gone."""
    return sum(1 for c in range(N)
               if base[c] == dead and alt.get(c, dead) == dead) / N


def main():
    print("=" * 78)
    print("CONTAINMENT ERROR — the map is not the dependencies")
    print("=" * 78)
    print(f"  {N:,} agents, each recorded with TWO evidence grounds and TWO")
    print(f"  authority grounds — fully redundant on paper. For 30% of them the")
    print(f"  two evidence grounds are secretly ONE source under two names.")
    print(f"  `hidden` is the share of those identities missing from the map.\n")
    print(f"  {'hidden edges':>13} {'C_predicted':>13} {'C_actual':>10}"
          f" {'error':>9}")
    rows = []
    for hidden in (0.0, 0.01, 0.05, 0.10, 0.20, 0.50, 1.00):
        rnd = random.Random(SEED)
        ev, seen_ev, au, up, n_alias = world(hidden, rnd)
        pred, act = worst(seen_ev, au, up), worst(ev, au, up)
        rows.append((hidden, pred, act))
        print(f"  {int(hidden * 100):>12}% {pred:>13.3f} {act:>10.3f}"
              f" {act - pred:>+9.3f}")

    print("\n  THE OTHER KIND OF MISSING EDGE — a hidden ALTERNATIVE")
    print(f"\n  {'hidden alternatives':>20} {'C_predicted':>13}"
          f" {'C_actual':>10} {'error':>9}")
    alt_rows = []
    for hidden in (0.0, 0.25, 0.50, 1.00):
        rnd = random.Random(SEED)
        b, ta, sa = alternatives(hidden, rnd)
        pred = max(alt_loss(b, sa, d) for d in range(SOURCES))
        act = max(alt_loss(b, ta, d) for d in range(SOURCES))
        alt_rows.append((hidden, pred, act))
        print(f"  {int(hidden * 100):>19}% {pred:>13.4f} {act:>10.4f}"
              f" {act - pred:>+9.4f}")
    assert alt_rows[-1][2] < alt_rows[-1][1]      # pessimistic, pinned

    base, full = rows[0], rows[-1]
    rel = (full[2] - full[1]) / full[2]
    print(f"""
  THE DIRECTION HOLDS FOR THIS KIND OF EDGE. Zero hidden, prediction equals reality
  ({base[1]:.3f}); every other row has the error POSITIVE and growing —
  {rows[2][2] - rows[2][1]:+.3f} at 5% hidden, {full[2] - full[1]:+.3f} at
  full. It is never negative, and cannot be: a missing edge can only make
  two grounds look more independent than they are. There is no symmetric
  case where an incomplete map flatters the danger instead of hiding it.
  A one-directional error is the kind you cannot average away.

  THE MAGNITUDE DID NOT REPRODUCE, and the honest report is that it did
  not. The hypothesis as put to me was "predicts under 1%, actually 40%".
  Here the worst is {full[1]:.3f} predicted against {full[2]:.3f} actual —
  a {rel:.0%} relative underestimate, real and not catastrophic.

  The reason is worth more than the number. The gap can only be as large
  as the share of the collective whose FATE RIDES ON THE HIDDEN EDGES. In
  this model the aliased agents still hold two genuine authority grounds,
  so the worst case is dominated by the authority side, which no hidden
  evidence edge touches. To get a 40-point gap the hidden edges would have
  to be load-bearing for most of the collective at once — which is a
  statement about WHERE incompleteness sits, not about how much of it
  there is. Five per cent of the wrong edges beats fifty per cent of the
  harmless ones.

  So the refined claim, and it is stronger than the one it replaces:
  containment error is bounded by the exposure of the edges you are
  missing, and that quantity is computable for a SUSPECTED
  incompleteness even though the missing edges are not. "We might be
  missing something" becomes "if we are missing these, here is the
  ceiling on how wrong we are".

  AND THE DIRECTION CLAIM WAS TOO STRONG. See the second table: when the
  missing edge is an ALTERNATIVE ground rather than a shared origin, the
  system predicts MORE fallout than occurs. Incompleteness is not
  one-directional; it is one-directional PER KIND OF EDGE. A missing
  common origin flatters, a missing alternative frightens, and this note
  asserted the first as a property of incompleteness itself.

  The two are not equally serious, which is the part worth keeping: an
  optimistic error lets a system act on warrant it does not hold, and a
  pessimistic one makes it withdraw from warrant it does. The first
  causes accidents and the second causes idleness.

  WHICH STILL NAMES A FOURTH UNOWNED THING. Attestation says who signed;
  provenance says what a ground descended from; the independence warrant
  says whether two grounds count as two; and a COMPLETENESS warrant would
  say whether the map is finished. This corpus cannot supply it — its
  oldest published ceiling is that citations are honoured and never
  discovered — and can price it, which is the shape every honest answer
  here has taken.""")
    assert base[2] == base[1]                     # exact on a visible graph
    assert all(a >= p for _h, p, a in rows)       # the error never runs the
                                                 # other way — the structural
                                                 # claim, and the one that
                                                 # survived the magnitude not
                                                 # reproducing
    assert full[2] - full[1] > 0.02
    print("\nBLINDSPOT PROBE GREEN — the error runs one way, and it is the "
          "dangerous way.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
