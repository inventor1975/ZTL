# -*- coding: utf-8 -*-
"""Arkadiy Miteiko's non-negotiable invariant, tested.

  With declared temporal uncertainty at zero and the temporal types collapsed to
  the assumptions of the existing probe, the generalized computation must reduce
  EXACTLY to the quantity measured by the original experiment. If it does not,
  we have changed the experiment rather than generalized it.

Two equalities are checked, not one. The second is the invariant; the first
exists because a duplication that had quietly drifted from the original would
make the second meaningless — it would compare the generalization against the
copy rather than against the experiment.

  1. the emitter's inline quantity  ==  probe_currentness.run(...)["acted"]
  2. the records-based measurement  ==  the emitter's inline quantity,
                                        with zero acts indeterminate

Run:  python3 db/currentness-input/test_reduction.py
"""
from __future__ import annotations

import copy
import importlib.util
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))

import emit_dataset  # noqa: E402
import measure as measure_mod  # noqa: E402

spec = importlib.util.spec_from_file_location("probe", HERE.parent / "probe_currentness.py")
probe = importlib.util.module_from_spec(spec)
assert spec.loader is not None
sys.modules["probe"] = probe
spec.loader.exec_module(probe)

LAGS = (0, 1, 2, 5, 10, 20, 50)
DRIFT, RATE = 20, 10


def main() -> int:
    print("=" * 74)
    print("REDUCTION — the generalization must collapse to the original quantity")
    print("=" * 74)
    print(f"  {'lag':>5} {'probe acted':>12} {'emitter':>9} {'records':>9}"
          f" {'indeterminate':>14}  verdict")
    ok = True
    for lag in LAGS:
        original = probe.run(lag, DRIFT, RATE)["acted"]
        data = emit_dataset.emit(lag, DRIFT, RATE)
        inline = data["probe_inline"]["acted"]
        m = measure_mod.measure(data)
        same = (inline == original
                and m["acted_certain"] == original
                and m["acted_indeterminate"] == 0)
        ok &= same
        print(f"  {lag:>5} {original:>12} {inline:>9} {m['acted_certain']:>9}"
              f" {m['acted_indeterminate']:>14}  {'REDUCES' if same else 'DRIFT'}")

    print()
    if not ok:
        print("  INVARIANT VIOLATED — this is a change of experiment, not a")
        print("  generalization. Reported as such rather than adjusted.")
        return 1
    print("  INVARIANT HOLDS on every lag: zero uncertainty collapses the")
    print("  interval to exactly the original number, with nothing indeterminate.")

    # And the other half: uncertainty must actually do something, or the
    # generalization is decorative.
    data = emit_dataset.emit(5, DRIFT, RATE)
    loose = copy.deepcopy(data)
    loose["uncertainty"] = {"effective_at": 2, "recorded_at": 2, "occurred_at": 1}
    m0, m1 = measure_mod.measure(data), measure_mod.measure(loose)
    print(f"""
  AND IT IS NOT DECORATIVE. The same run, re-read with a declared bound of
  +/-2 steps on the change times and +/-1 on the acts:

      certain          {m0['acted_certain']:>6}  ->  {m1['acted_certain']:>6}
      indeterminate    {m0['acted_indeterminate']:>6}  ->  {m1['acted_indeterminate']:>6}
      upper bound      {m0['acted_upper_bound']:>6}  ->  {m1['acted_upper_bound']:>6}

  The number the experiment used to report now sits inside an interval, and
  the acts whose membership the records cannot settle are counted rather than
  assigned to whichever side is convenient.""")
    if m1["acted_indeterminate"] == 0:
        print("\n  WARNING: uncertainty produced no indeterminacy — check the bounds.")
        return 1
    print("\nREDUCTION TEST GREEN.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
