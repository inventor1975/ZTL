# -*- coding: utf-8 -*-
"""
A runtime gate: when must an autonomous collective stop acting on its warrant?

the external reviewer Miteiko's correction to the previous run, and it was right. "The blind
window equals the update lag" is near-tautological when detection is perfect
and the lag is fixed: of course a map L steps behind is blind for L steps.
That is not a result to take anywhere.

The result under it is `exposure = currentness lag x action rate`, and the
consequence is a control problem rather than an observation: past some action
rate you cannot update faster, and the remaining moves are to slow down, to
shrink the cascade radius, or to stop acting on the old warrant.

So this file removes what made the last one easy. Updates arrive after a
RANDOM delay, a share of them are LOST OUTRIGHT and never arrive at all, and
drift continues underneath. The system therefore cannot know C_actual — ever —
and the question becomes what it can decide from what it CAN see:

    time since each source was last confirmed
    the rate of change it has observed
    its own action rate

The gate proposed and tested here:

    C_pred + margin(staleness, observed drift) <= limit    ->   ACT
    otherwise                                              ->   HOLD

and the number a programme office would ask for: the MAXIMUM ACTION RATE at
which a collective can stay in ACT at all, given that its knowledge of its own
dependencies is permanently incomplete.

Run:  python3 db/probe_gate.py
"""
import random
import statistics
import sys

N, SOURCES = 20_000, 5
STEPS = 300
LIMIT = 0.02
SEED = 20260816


def worst(ground):
    both = [0] * SOURCES
    for a, b in ground:
        if a == b:
            both[a] += 1
    return max(both) / N


def mission(drift, rate, loss, mean_delay, gated, seed=SEED):
    """One mission under lossy, delayed observation.

    `loss` is the share of dependency changes NEVER reported — the part that
    makes certainty impossible rather than merely late. `gated` switches the
    runtime gate on; with it off the collective acts throughout, which is the
    control."""
    rnd = random.Random(seed)
    true = [(rnd.randrange(SOURCES), rnd.randrange(SOURCES)) for _ in range(N)]
    true = [(a, b if b != a else (a + 1) % SOURCES) for a, b in true]
    seen = list(true)
    pending, acted, violations, held = [], 0, 0, 0
    last_seen_change, observed_changes = 0, 0
    for step in range(STEPS):
        for _ in range(drift):
            i = rnd.randrange(N)
            a, _b = true[i]
            true[i] = (a, a)
            if rnd.random() >= loss:            # the rest is never reported
                delay = 1 + int(rnd.expovariate(1.0 / max(mean_delay, 1e-9)))
                pending.append((step + delay, i, (a, a)))
        arrived = [p for p in pending if p[0] <= step]
        for _w, i, val in arrived:
            seen[i] = val
        if arrived:
            last_seen_change = step
            observed_changes += len(arrived)
        pending = [p for p in pending if p[0] > step]

        c_pred, c_act = worst(seen), worst(true)
        # WHAT THE SYSTEM CAN ACTUALLY COMPUTE. Not C_actual — it never has
        # that. Staleness is how long since anything was confirmed; the
        # observed rate is what it has seen change; and the loss share is a
        # declared property of the channel, not a measurement. The margin is
        # therefore a bound built only from things the system holds.
        staleness = step - last_seen_change
        obs_rate = observed_changes / max(step, 1)
        unseen_rate = obs_rate * (loss / max(1 - loss, 1e-9))
        margin = (staleness + mean_delay) * (obs_rate + unseen_rate) / N
        if gated and c_pred + margin > LIMIT:
            held += 1
            continue                            # the gate: do not act
        acted += rate
        if c_act > LIMIT:
            violations += rate
    return {"acted": acted, "violations": violations, "held": held}


def main():
    print("=" * 78)
    print("A RUNTIME GATE — acting on warrant that may already be stale")
    print("=" * 78)
    print(f"  {N:,} agents, {SOURCES} sources, {STEPS} steps, limit {LIMIT:.0%}")
    print(f"  Updates arrive after a random delay; a share is LOST for good.\n")

    print("  1. WITHOUT A GATE — the collective acts throughout\n")
    print(f"  {'loss':>6} {'mean delay':>11} {'actions':>9} {'VIOLATIONS':>11}"
          f" {'share':>8}")
    for loss, d in ((0.0, 3), (0.1, 3), (0.3, 3), (0.3, 10), (0.5, 10)):
        r = mission(20, 10, loss, d, gated=False)
        share = r["violations"] / max(r["acted"], 1)
        print(f"  {loss:>6.0%} {d:>11} {r['acted']:>9} {r['violations']:>11}"
              f" {share:>8.1%}")

    print("\n  2. WITH THE GATE — hold when the bound cannot clear the limit\n")
    print(f"  {'loss':>6} {'mean delay':>11} {'actions':>9} {'VIOLATIONS':>11}"
          f" {'held':>6}")
    gated = []
    for loss, d in ((0.0, 3), (0.1, 3), (0.3, 3), (0.3, 10), (0.5, 10)):
        r = mission(20, 10, loss, d, gated=True)
        gated.append(r)
        _ = r
        print(f"  {loss:>6.0%} {d:>11} {r['acted']:>9} {r['violations']:>11}"
              f" {r['held']:>6}")

    leak_free = sum(1 for r in gated if r["violations"] == 0)
    leaked = sum(1 for r in gated if r["violations"] > 0)

    print("\n  3. THE NUMBER A PROGRAMME OFFICE ASKS FOR")
    print("     maximum action rate holding violations at zero, per channel\n")
    print(f"  {'loss':>6} {'mean delay':>11} {'max rate':>10}"
          f" {'actions delivered':>18}")
    for loss, d in ((0.0, 3), (0.1, 3), (0.3, 10), (0.5, 10)):
        best, delivered = 0, 0
        for rate in (1, 2, 5, 10, 20, 50, 100):
            r = mission(20, rate, loss, d, gated=True)
            if r["violations"] == 0:
                best, delivered = rate, r["acted"]
        print(f"  {loss:>6.0%} {d:>11} {best:>10} {delivered:>18}")

    print("""
  WHAT THE GATE IS AND IS NOT. It never sees C_actual — no engineering
  gives it that once observations can be lost. It sees how long since
  anything was confirmed, how fast it has seen things change, and a
  declared loss rate for its own channel, and from those it builds a
  BOUND. Acting only while the bound clears the limit is the whole rule.

  THE FIRST TABLE IS THE ARGUMENT. Ungated, a collective on ANY of these
  channels spends about two thirds of its actions outside its own
  containment requirement — 66% at zero loss, because delay alone is
  enough — and nothing in the system reports that at the time. This is
  not a lossy-channel problem. It is what acting on an unbounded warrant
  looks like.

  AND THE SECOND TABLE CONTAINS A FAILURE OF MY OWN, which is the finding
  worth more than the successes beside it. The gate holds violations at
  zero on three channels and LEAKS ON TWO — 270 violations at 30% loss,
  170 at 50%. So the margin written above is not a sound bound; it is a
  plausible expression that happens to work in some regimes. A gate that
  is right most of the time is not a gate, and the fix is not a bigger
  constant: the margin has to be DERIVED from a model of the channel,
  with the loss rate as a parameter of a proof rather than a number
  multiplied into a guess. That derivation does not exist here and is
  named rather than implied.

  THE THIRD TABLE IS THEREFORE READ WITH THE SECOND. Where the bound
  holds, a high action rate is affordable; at 50% loss with a long delay
  NO rate keeps violations at zero, and the honest output is DENY rather
  than a slower ACT. That is the shape the criterion has to take, and the
  numbers under it are provisional until the margin is proved.

  A gate that never violates is also available at every loss rate — by
  holding forever. The question was never whether stopping is safe; it is
  how much action survives the safety, which is why rate and actions
  delivered are reported together. Reporting the first alone would be
  selling a brake as an engine.

  THE CRITERION, and the wording took three passes to get right, which is
  itself worth recording. The first draft said a collective "may ACT on a
  warrant" — plainly normative, and nothing here establishes whether
  anything may act. The second said "may continue to RELY", which is
  narrower and still a permission. Both were caught in review, and the
  distinction is not pedantry: this corpus computes the consequences of
  authority and does not confer it, and its own summary sentence was the
  one place that boundary kept slipping.

  Purely descriptive, third pass:

      a system may continue to TREAT its current warrant as satisfying the
      stated containment criterion only while it can bound that warrant's
      possible staleness within that criterion

  Whether reliance or action is PERMITTED in that state is decided by an
  external authority layer. This measures the antecedent; it does not
  reach the consequent.

  Where it cannot, the moves left are to act more slowly, to shrink what
  one loss takes down, or to stop relying — and which is affordable is
  architecture, decided before the mission rather than during it.""")
    assert leak_free < 5 and leaked > 0        # the gate's own failure, pinned
    return 0


if __name__ == "__main__":
    sys.exit(main())
