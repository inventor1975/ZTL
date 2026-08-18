# -*- coding: utf-8 -*-
"""
The probes' side of the ground record — one import, so no probe repeats it.

A probe wraps its sweep:

    for lag in swept('lag', (0, 1, 2, 5, 10, 20, 50)):

and calls `save_ground(__file__)` at the end. What the run actually varied is
then written by the LOOP rather than typed beside it, and a sentence claiming
to quantify over a dimension can be checked against the sweep instead of
against its author's memory. The reasoning is in `lab/swept.py`.

`lab/` is untracked working material and MUST NOT be a dependency of anything
in `db/`. If it is absent these become the identity function and a no-op, and
every probe runs exactly as before — the recorder is an instrument, not a
component. That is checked by `_selftest` below.
"""
import os
import sys

_LAB = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                    "lab")

try:
    sys.path.insert(0, _LAB)
    from swept import swept, save as _save            # noqa: F401
    HAVE_GROUND = True
except Exception:                                     # pragma: no cover
    HAVE_GROUND = False

    def swept(_dimension, values):
        return list(values)

    def _save(_probe_name):
        return {}


def save_ground(probe_file):
    """Record this run's sweeps under the probe's own name and say so. Silent
    when nothing was recorded, so a probe without lab/ prints what it always
    printed."""
    name = os.path.splitext(os.path.basename(probe_file))[0]
    g = _save(name)
    if g:
        print("\n  ground recorded by the act (lab/ground.json): "
              + ", ".join(f"{k}={len(v)}" for k, v in sorted(g.items())))
    return g


def _selftest():
    print("=" * 78)
    print("_ground — the recorder must not be a dependency")
    print("=" * 78)
    print(f"\n  lab/ present : {HAVE_GROUND}")
    vals = swept("selftest_dimension", (1, 2, 3))
    print(f"  swept() yields its values either way : {vals}")
    assert vals == [1, 2, 3], "swept must be transparent to the loop"
    print("\n  With lab/ absent both become no-ops and every probe runs")
    print("  unchanged. The record is an instrument, not a component.")
    return 0


if __name__ == "__main__":
    sys.exit(_selftest())
