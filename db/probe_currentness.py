# -*- coding: utf-8 -*-
"""
Currentness — the window of false containment, measured.

the external reviewer Miteiko's dynamic experiment, and his terminology correction taken
with it: a system can almost never prove there are no unknown edges, so the
honest object is a BOUNDED completeness warrant — this scope, this schema,
this moment, sufficient for this decision. Which makes the moment itself a
variable, and that variable is what this file measures.

The sequence he specified:

  t1  an agent quietly re-points one ground to the source its other ground
      already uses — the two are now one and nobody has said so
  t2  the dependency map learns of it
  t3  the independence warrant is withdrawn
  t4  the downstream warrant is recomputed

Everything between t1 and t4 is a window in which the system reports
containment it does not have, and acts. So the measurements are not C but:

  stale       steps between the change and the map catching up
  acted       consequential actions taken inside the window
  C_pred      what the system believed at the time
  C_act       what was already true

And the number a designer needs: the LARGEST update lag at which false
containment stays inside a stated limit, as a function of how fast the
collective acts.

Run:  python3 db/probe_currentness.py
"""
import random
import sys

from _ground import swept, save_ground    # the sweep records what it varied

N, SOURCES = 20_000, 5
STEPS = 200
LIMIT = 0.02                  # containment requirement: worst loss under 2%
SEED = 20260816


def worst(ground):
    """Worst single-source loss: the agents whose BOTH grounds are that one."""
    both = [0] * SOURCES
    for a, b in ground:
        if a == b:
            both[a] += 1
    return max(both) / N


def run(lag, drift, actions_per_step, seed=SEED):
    """One mission. `drift` agents per step re-point a ground; the map is
    `lag` steps behind; the collective takes `actions_per_step` consequential
    actions throughout."""
    rnd = random.Random(seed)
    true = [(rnd.randrange(SOURCES), rnd.randrange(SOURCES)) for _ in range(N)]
    true = [(a, b if b != a else (a + 1) % SOURCES) for a, b in true]
    seen = list(true)                       # at t0 the map is exact
    history, stale_spans, acted, worst_gap = [], [], 0, 0.0
    pending = []                            # (step_it_becomes_visible, index)
    first_bad = None
    for step in range(STEPS):
        for _ in range(drift):
            i = rnd.randrange(N)
            a, _b = true[i]
            true[i] = (a, a)                # the two grounds become one
            pending.append((step + lag, i, (a, a)))
        for when, i, val in [p for p in pending if p[0] <= step]:
            seen[i] = val
        pending = [p for p in pending if p[0] > step]

        c_pred, c_act = worst(seen), worst(true)
        blind = c_act > LIMIT >= c_pred
        if blind:
            acted += actions_per_step
            if first_bad is None:
                first_bad = step
            worst_gap = max(worst_gap, c_act - c_pred)
        elif first_bad is not None:
            stale_spans.append(step - first_bad)
            first_bad = None
        history.append((step, c_pred, c_act, blind))
    if first_bad is not None:
        stale_spans.append(STEPS - first_bad)
    return {"acted": acted, "gap": worst_gap,
            "stale": max(stale_spans) if stale_spans else 0,
            "blind_steps": sum(1 for _s, _p, _a, b in history if b)}


def main():
    print("=" * 78)
    print("CURRENTNESS — the window in which containment is reported and gone")
    print("=" * 78)
    print(f"  {N:,} agents on {SOURCES} sources; containment requirement:")
    print(f"  worst single-source loss under {LIMIT:.0%}. A mission of {STEPS}")
    print(f"  steps; each step some agents quietly re-point one ground onto")
    print(f"  the source their other ground already uses.\n")

    drift, rate = 20, 10
    print(f"  drift {drift} agents/step, {rate} consequential actions/step\n")
    print(f"  {'update lag':>11} {'blind steps':>12} {'longest window':>15}"
          f" {'actions in it':>14} {'worst gap':>11}")
    rows = []
    for lag in swept('lag', (0, 1, 2, 5, 10, 20, 50)):
        r = run(lag, drift, rate)
        rows.append((lag, r))
        print(f"  {lag:>11} {r['blind_steps']:>12} {r['stale']:>15}"
              f" {r['acted']:>14} {r['gap']:>11.4f}")

    print(f"""
  A PREDICTION OF MINE, REFUTED BY ITS OWN TABLE. This file first said
  "lag zero is not safe" — that even a perfectly current map learns after
  the fact. It does not, in this model: at lag 0 the blind window is zero
  steps and zero actions. I wrote the conclusion before reading the run,
  which is the failure this corpus exists to make expensive, so it stays
  written down.

  WHAT THE RUN SAYS INSTEAD IS SHARPER. The window of false containment
  is EXACTLY the update lag — one step of lag, one blind step; fifty, and
  fifty. Not approximately and not on average: the drift is invisible for
  precisely as long as the map is behind, and visible the moment it is
  not. So the actions taken under a containment the system no longer has
  are exactly lag x rate, and the designer's rule needs no simulation:

      max tolerable lag = action budget / consequential actions per step

  The gap itself grows with lag too ({rows[-1][1]['gap']:.4f} at fifty
  steps against {rows[3][1]['gap']:.4f} at five), so a long lag costs
  twice: more actions taken blind, and a larger error in each of them.""")
    # the refuted prediction and the law that replaced it, both pinned
    assert rows[0][1]["blind_steps"] == 0
    for lag, r in rows:
        assert r["blind_steps"] == lag and r["stale"] == lag
    print("\n  Checked on every row: blind steps == update lag, exactly.")
    print("\n  THE NUMBER A DESIGNER ASKS FOR: the largest lag that keeps")
    print("  false-containment actions under a budget, per action rate.\n")
    print(f"  {'actions/step':>13} {'budget 50':>11} {'budget 200':>12}"
          f" {'budget 1000':>13}")
    for rate2 in (1, 5, 10, 50):
        cells = []
        for budget in swept('budget', (50, 200, 1000)):
            ok = [lag for lag in (0, 1, 2, 5, 10, 20, 50)
                  if run(lag, drift, rate2)["acted"] <= budget]
            cells.append(str(max(ok)) if ok else "none")
        print(f"  {rate2:>13} {cells[0]:>11} {cells[1]:>12} {cells[2]:>13}")

    print("""
  READ THE COLUMNS, NOT THE CELLS. The tolerable lag is not a property of
  the system; it falls as the collective acts faster, and at a high enough
  rate no lag is tolerable at all — the honest answer there is not a
  better update but a lower action rate, or a smaller cascade radius, and
  that is an architectural decision rather than an engineering one.

  SO THE ORDER IS FIVE, NOT FOUR, and the fifth is his:

    identity              who signed a ground
    provenance            what it descended from
    independence          whether two grounds count as two
    bounded completeness  whether the map is finished ENOUGH, for this
                          scope and this decision
    CURRENTNESS           whether that judgement is still true NOW

  A full map is not sufficient if it stops being current faster than the
  system withdraws reliance. This corpus supplies none of the five; it
  computes what each of them is worth, and that is the fourth time in
  three days a run has priced a primitive nobody owns.""")
    assert rows[-1][1]["acted"] > rows[0][1]["acted"]
    save_ground(__file__)
    print("\nCURRENTNESS PROBE GREEN — the window IS the lag, exactly.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
