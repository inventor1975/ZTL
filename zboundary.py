# -*- coding: utf-8 -*-
"""
zboundary — judging inside a DECLARED world of admissible readings.

An unverified ground normally stands for every reading of itself: the judge
quantifies over all of them. Sometimes a reader declares that some readings are
not in view at all — a jurisdiction that declines to consider one, a hypothesis
that sets one aside, a fiction that never contains it. None of those makes the
reading FALSE (for false there is F); it makes it out of view, and the two are
different things.

That declaration is a PREMISE, never a discovery, so this module prints what it
costs:

    verdict(phi, env, boundary) -> dict
        verdict      the value, or E when the boundary admits nothing
        admitted     the readings still in view
        excluded     the readings the boundary removed
        defeating    those of the excluded that would have CHANGED the verdict
        note         the reading of that, in one sentence

`defeating` is the line that matters. If it is non-empty, the verdict rests on
the boundary rather than on what was disclosed — and the excluded readings are
named, so whoever has standing to decide admissibility can contest them rather
than the abstraction.

An empty boundary yields E, not a vacuous T. This is the corpus's own letter:
`znum.py` — "judging IS quantification over readings; E is what happens when
there is nothing to quantify over" — and ZTLStudio renders it as «E — нечего
читать». A world with no admissible readings is not a world.

WHERE THIS SITS. This is the JUDGE. The studio calls it; it does not call the
studio, and it imports nothing from `tool/`. The same function is available to
`ztljudge`, to a downstream consumer, and to any harness that needs to judge a
partial disclosure inside a declared boundary.

The theorems behind the behaviour are in `lean/ContextClosure.lean`, and the
measured trade-off in `experiments/context-closure-001/`.
"""

from itertools import product

from ztl import T, F, Z, ev
from znum import E

__all__ = ["admissible", "verdict", "E"]


def _marked(env):
    return sorted(a for a, v in env.items() if v == Z)


def admissible(env, boundary):
    """Completions of the unverified grounds that the declared boundary keeps.

    `boundary` maps an atom to the values NOT in view, e.g. {"b": ["T"]}."""
    boundary = boundary or {}
    marks = _marked(env)
    out = []
    for combo in product((T, F), repeat=len(marks)):
        comp = dict(zip(marks, combo))
        if any(v in boundary.get(a, ()) for a, v in comp.items()):
            continue
        out.append(comp)
    return out


def verdict(phi, env, boundary=None):
    """Judge `phi` under `env` inside the declared boundary, and bill it."""
    value = ev(phi, env)
    marks = _marked(env)
    boundary = boundary or {}

    if not boundary or not marks:
        return {"verdict": value, "admitted": None, "excluded": [],
                "defeating": [], "note": "no boundary declared — every reading"
                                         " of the unverified is in view"}

    admitted, excluded, defeating = [], [], []
    for combo in product((T, F), repeat=len(marks)):
        comp = dict(zip(marks, combo))
        label = ", ".join(f"{a}={v}" for a, v in comp.items())
        if any(v in boundary.get(a, ()) for a, v in comp.items()):
            excluded.append(label)
            env2 = dict(env)
            env2.update(comp)
            if ev(phi, env2) != value:
                defeating.append(label)
        else:
            admitted.append(label)

    if not admitted:
        return {"verdict": E, "admitted": [], "excluded": excluded,
                "defeating": defeating,
                "note": "E — nothing to read: the declared boundary admits no"
                        " reading at all, so there is nothing to quantify over."
                        " Not warranted and not refuted; a boundary that"
                        " excludes everything is not a boundary but a"
                        " contradiction"}

    return {"verdict": value, "admitted": admitted, "excluded": excluded,
            "defeating": defeating,
            "note": ("the verdict rests on the BOUNDARY, not on what was"
                     " disclosed: the excluded readings would have changed it,"
                     " and they are named so that whoever may decide"
                     " admissibility can contest them"
                     if defeating else
                     "the boundary excluded nothing that could have changed the"
                     " verdict — it is not carrying the conclusion")}


if __name__ == "__main__":
    claim = ("not", ("and", "a", "b"))
    env = {"a": T, "b": Z}
    print("=" * 70)
    print("zboundary — judging inside a declared world")
    print("=" * 70)
    for name, b in (("no boundary", None),
                    ("b excludes T", {"b": ["T"]}),
                    ("b excludes F", {"b": ["F"]}),
                    ("b excludes T and F", {"b": ["T", "F"]})):
        r = verdict(claim, env, b)
        print(f"\n  {name}")
        print(f"    verdict   {r['verdict']}")
        print(f"    in view   {r['admitted']}")
        print(f"    out       {r['excluded']}  of those decisive: {r['defeating']}")
        print(f"    {r['note'][:66]}")
    print("\n" + "=" * 70)
    print("ZBOUNDARY GREEN — the judge decides; the studio only displays.")
