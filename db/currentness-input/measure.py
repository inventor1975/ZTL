# -*- coding: utf-8 -*-
"""The measurement, computed from records rather than from live state.

Adrián Lerer's redesign of A8, implemented. The old rule compared declared clock
skew against the smallest observed lag and refused the whole dataset when they
were not separable. It was too strict — one outlier killed a usable dataset —
and too weak, because it treated every timestamp as the same institutional event
when real records carry several legally distinct temporalities.

What replaces it is a SENSITIVITY test, and the unit of judgement moves from the
dataset to the individual act.

Each timestamp carries a declared uncertainty bound. From those bounds two blind
sets are derived: the steps that are blind under EVERY admissible reading, and
the steps that are blind under SOME admissible reading. An act whose own interval
lies wholly inside the first is certainly inside the window; one that misses the
second entirely is certainly outside; anything else is INDETERMINATE — the
records cannot settle it, and saying either would be inventing the answer.

So the headline quantity stops being a number and becomes an interval:

    acted_certain                  acts certainly inside the window
    acted_certain + indeterminate  the upper bound

Arkadiy Miteiko's invariant, which this must satisfy: with every declared
uncertainty at zero the two sets coincide, no act is indeterminate, and the
interval collapses to exactly the quantity the original probe measures.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path


def _worst(ground: list[list[int]], sources: int, n: int) -> float:
    both = [0] * sources
    for a, b in ground:
        if a == b:
            both[a] += 1
    return max(both) / n


def blind_sets(d: dict) -> tuple[set[int], set[int]]:
    """(certainly blind, possibly blind), over the declared temporal bounds.

    A change's effective time may sit anywhere in its bound, and so may its
    recorded time. Blindness at a step needs the actual state to breach the
    threshold while the recorded state does not, so the two extremes are taken
    on purpose: the reading that makes the window widest, and the one that makes
    it narrowest. Every admissible reading lies between them.
    """
    w = d["world"]
    n, sources, steps = w["subjects"], w["sources"], w["steps"]
    thr = d["requirement"]["threshold"]
    ue = d["uncertainty"].get("effective_at", 0)
    ur = d["uncertainty"].get("recorded_at", 0)

    def run(eff_shift: int, rec_shift: int) -> set[int]:
        true = [list(g) for g in w["initial"]]
        seen = [list(g) for g in w["initial"]]
        by_eff: dict[int, list[dict]] = {}
        by_rec: dict[int, list[dict]] = {}
        for c in d["changes"]:
            by_eff.setdefault(c["effective_at"] + eff_shift, []).append(c)
            by_rec.setdefault(c["recorded_at"] + rec_shift, []).append(c)
        out: set[int] = set()
        for step in range(steps):
            for c in by_eff.get(step, []):
                true[c["subject"]] = list(c["new_ground"])
            for c in by_rec.get(step, []):
                seen[c["subject"]] = list(c["new_ground"])
            if _worst(true, sources, n) > thr >= _worst(seen, sources, n):
                out.add(step)
        return out

    # widest: the breach happens as early as it may, the record catches up as
    # late as it may. narrowest: the mirror image.
    widest = run(-ue, +ur)
    narrowest = run(+ue, -ur)
    return (widest & narrowest), (widest | narrowest)


def measure(d: dict) -> dict:
    certain_blind, possible_blind = blind_sets(d)
    ua = d["uncertainty"].get("occurred_at", 0)

    certain = indeterminate = outside = 0
    witnesses: list[str] = []
    for act in d["acts"]:
        lo, hi = act["occurred_at"] - ua, act["occurred_at"] + ua
        span = set(range(lo, hi + 1))
        if span <= certain_blind:
            certain += 1
        elif span & possible_blind:
            indeterminate += 1
            if len(witnesses) < 5:
                witnesses.append(act["act_id"])
        else:
            outside += 1

    return {
        "record_class": "CURRENTNESS_MEASUREMENT",
        "acted_certain": certain,
        "acted_indeterminate": indeterminate,
        "acted_upper_bound": certain + indeterminate,
        "acts_outside": outside,
        "blind_steps_certain": len(certain_blind),
        "blind_steps_possible": len(possible_blind),
        "indeterminate_witnesses": witnesses,
        "reduces_to_a_number": indeterminate == 0,
    }


if __name__ == "__main__":
    data = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
    print(json.dumps(measure(data), indent=2))
