# -*- coding: utf-8 -*-
"""Make the simulation emit the records it has always implied.

`probe_currentness.py` computes its answer from state it holds in memory. A
records-based measurement cannot; it must reconstruct the same answer from
evidence. This file runs the same world and writes down what a record keeper
would have written down, so the two can be compared on the same run.

It also recomputes the probe's own quantity inline, and the reduction test
asserts that number against `probe_currentness.run` — otherwise a faithful-looking
duplication could drift from the original and the whole comparison would be
measuring the duplication instead.

Run:  python3 db/currentness-input/emit_dataset.py > /tmp/emitted.json
"""
from __future__ import annotations

import json
import random
import sys

N, SOURCES = 20_000, 5
STEPS = 200
LIMIT = 0.02
SEED = 20260816


def worst(ground: list[tuple[int, int]]) -> float:
    both = [0] * SOURCES
    for a, b in ground:
        if a == b:
            both[a] += 1
    return max(both) / N


def emit(lag: int, drift: int, actions_per_step: int, seed: int = SEED,
         receipt_offset: int = 2) -> dict:
    rnd = random.Random(seed)
    true = [(rnd.randrange(SOURCES), rnd.randrange(SOURCES)) for _ in range(N)]
    true = [(a, b if b != a else (a + 1) % SOURCES) for a, b in true]
    initial = [list(g) for g in true]
    seen = list(true)

    changes: list[dict] = []
    acts: list[dict] = []
    pending: list[tuple[int, int, tuple[int, int]]] = []
    acted = 0
    blind_steps = 0

    for step in range(STEPS):
        for _ in range(drift):
            i = rnd.randrange(N)
            a, _b = true[i]
            true[i] = (a, a)
            pending.append((step + lag, i, (a, a)))
            changes.append({
                # The receipt time is INVENTED and declared as invented in
                # SENSITIVITY-PREDECLARATION-v0.1.md. The simulation never had
                # one; it exists so that two interval definitions exist to
                # compare. It is not a claim about real institutions.
                "change_id": f"c{len(changes)}",
                "subject": i,
                "new_ground": [a, a],
                "effective_at": step,
                "received_at": step + receipt_offset,
                "recorded_at": step + lag,
            })
        for when, i, val in [p for p in pending if p[0] <= step]:
            seen[i] = val
        pending = [p for p in pending if p[0] > step]

        blind = worst(true) > LIMIT >= worst(seen)
        if blind:
            acted += actions_per_step
            blind_steps += 1
        for k in range(actions_per_step):
            acts.append({"act_id": f"a{step}-{k}", "occurred_at": step})

    return {
        "schema_version": "CURRENTNESS-INPUT-v0.3-draft",
        "world": {"subjects": N, "sources": SOURCES, "steps": STEPS, "initial": initial},
        "requirement": {
            "declared_by": "the simulation, standing in for a record holder",
            "predicate": "worst_single_source_share",
            "threshold": LIMIT,
        },
        "uncertainty": {"effective_at": 0, "recorded_at": 0, "occurred_at": 0},
        "changes": changes,
        "acts": acts,
        "probe_inline": {"acted": acted, "blind_steps": blind_steps, "lag": lag,
                         "drift": drift, "actions_per_step": actions_per_step},
    }


if __name__ == "__main__":
    lag = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    json.dump(emit(lag, 20, 10), sys.stdout)
