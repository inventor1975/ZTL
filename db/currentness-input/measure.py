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


#: Condition 4, unknown preservation. These are four different institutional
#: states and none may impersonate another: an act settled inside the window, an
#: act settled outside it, and an act the records cannot place. "Not established"
#: is not "established false" — the correction is Arkadiy Miteiko's.
#:
#: Condition 5, evidence-universe boundedness. The name says *within available
#: evidence* on purpose. Another contemporaneous source, a statutory
#: presumption, or transaction evidence could in principle settle what these
#: records cannot, so this must never be read as unknowable in principle.
CERTAINLY_INSIDE = "CERTAINLY_INSIDE_WINDOW"
CERTAINLY_OUTSIDE = "CERTAINLY_OUTSIDE_WINDOW"
UNRESOLVED = "UNRESOLVED_WITHIN_AVAILABLE_EVIDENCE"


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

    # Condition 6, act-level conservation: every act ends in exactly one state.
    # Counted into a per-act map rather than three counters, so a disappearance
    # or a double count is a structural impossibility rather than a thing to
    # remember not to do.
    state: dict[str, str] = {}
    for act in d["acts"]:
        lo, hi = act["occurred_at"] - ua, act["occurred_at"] + ua
        span = set(range(lo, hi + 1))
        if span <= certain_blind:
            state[act["act_id"]] = CERTAINLY_INSIDE
        elif span & possible_blind:
            state[act["act_id"]] = UNRESOLVED
        else:
            state[act["act_id"]] = CERTAINLY_OUTSIDE
    if len(state) != len(d["acts"]):
        raise ValueError("act-level conservation violated: an act_id is duplicated")

    certain = sum(1 for v in state.values() if v == CERTAINLY_INSIDE)
    unresolved = sum(1 for v in state.values() if v == UNRESOLVED)
    outside = sum(1 for v in state.values() if v == CERTAINLY_OUTSIDE)

    return {
        "record_class": "CURRENTNESS_EPISTEMIC_CLASSIFICATION",
        # Condition 2: named, so a later reader can check that this is still the
        # quantity the experiment was designed to measure and not a neighbour.
        "proposition_tested": (
            "the act occurred inside an interval during which the recorded state "
            "satisfied the declared containment requirement and the actual state "
            "did not"
        ),
        "evidence_universe": d.get("scope", {}).get(
            "label", "the records supplied to this run, and nothing else"
        ),
        "acted_certainly_inside": certain,
        "acted_unresolved": unresolved,
        "acted_certainly_outside": outside,
        "acted_upper_bound": certain + unresolved,
        "acts_total": len(state),
        "conservation_holds": certain + unresolved + outside == len(d["acts"]),
        "blind_steps_certain": len(certain_blind),
        "blind_steps_possible": len(possible_blind),
        "unresolved_witnesses": [k for k, v in state.items() if v == UNRESOLVED][:5],
        "reduces_to_a_number": unresolved == 0,
        # Conditions 7 and 8: this record classifies evidence and stops. It
        # carries no admissibility consequence, and cannot: what "unresolved"
        # means for whether an act may be relied upon is an institutional rule,
        # and this layer has no authority to invent one.
        "admissibility_consequence": None,
        "admissibility_note": (
            "epistemic classification only. Whether an unresolved act may be "
            "relied upon for a given use requires a separately identified "
            "institutional authority and is deliberately not computed here."
        ),
    }


if __name__ == "__main__":
    data = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
    print(json.dumps(measure(data), indent=2))
