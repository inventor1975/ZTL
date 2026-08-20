# -*- coding: utf-8 -*-
"""The interval-sensitivity experiment, run exactly as predeclared.

Protocol frozen in SENSITIVITY-PREDECLARATION-v0.1.md before any result was
seen: the two interval definitions, the evidence universe, the treatment of the
unresolved state, both metrics, and the material-divergence condition.

Arkadiy Miteiko's boundary, which this file obeys and prints rather than
assumes: the run measures how classification changes under alternative
predeclared interval definitions and infers NOTHING from the answer — not which
interval is institutionally correct, not whether a declaration requirement is
warranted, not what disposition follows.
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import emit_dataset  # noqa: E402
import measure as M  # noqa: E402

LAG, DRIFT, RATE = 5, 20, 10
OFFSETS = (1, 2, 3)
M1_THRESHOLD, M2_THRESHOLD = 0.05, 0.10


def classify(data: dict, opens: str) -> dict[str, str]:
    certain, possible = M.blind_sets(data, opens)
    out: dict[str, str] = {}
    for act in data["acts"]:
        t = act["occurred_at"]
        out[act["act_id"]] = M.CERTAINLY_INSIDE if t in certain else (
            M.UNRESOLVED if t in possible else M.CERTAINLY_OUTSIDE
        )
    return out


def main() -> int:
    print("=" * 74)
    print("INTERVAL SENSITIVITY — predeclared, and inferring nothing")
    print("=" * 74)
    print("  A = normative currentness   opens at effectiveness, closes at record")
    print("  B = response duty           opens at receipt,       closes at record")
    print(f"  evidence universe: lag {LAG}, drift {DRIFT}, {RATE} acts/step, seed 20260816")
    print("  the receipt timestamp is INVENTED and declared as invented\n")
    print(f"  {'offset':>7} {'inside A':>9} {'inside B':>9} {'M1 changed':>11}"
          f" {'M2 rel.':>9}  verdict")

    verdicts = []
    for off in OFFSETS:
        data = emit_dataset.emit(LAG, DRIFT, RATE, receipt_offset=off)
        a = classify(data, "effective_at")
        b = classify(data, "received_at")
        inside_a = sum(1 for v in a.values() if v == M.CERTAINLY_INSIDE)
        inside_b = sum(1 for v in b.values() if v == M.CERTAINLY_INSIDE)
        m1 = sum(1 for k in a if a[k] != b[k]) / len(a)
        m2 = abs(inside_b - inside_a) / inside_a if inside_a else 0.0
        material = m1 >= M1_THRESHOLD or m2 >= M2_THRESHOLD
        verdicts.append(material)
        print(f"  {off:>7} {inside_a:>9} {inside_b:>9} {m1:>10.3f}"
              f" {m2:>9.3f}  {'MATERIAL' if material else 'not material'}")

    stable = len(set(verdicts)) == 1
    print()
    if not stable:
        print("  UNSTABLE ACROSS OFFSETS. The verdict flips with the invented")
        print("  receipt offset, so it is an artefact of that choice rather than")
        print("  a property of interval selection. Reported as instability.")
        return 1

    if verdicts[0]:
        print("  RESULT: MATERIAL at every offset tested.")
        print("""
  WHAT THIS LICENSES, and nothing further. Choosing the interval silently is
  consequential in this evidence universe: the same records, read under two
  predeclared definitions, classify a different set of acts. It does NOT
  establish which interval is institutionally correct, that a declaration
  requirement is warranted, or what may be relied upon. Those are questions of
  warrant and admissibility and are not computed here.""")
    else:
        print("  RESULT: NOT MATERIAL at every offset tested.")
        print("""
  AND CONVERGENCE LICENSES LESS THAN DIVERGENCE WOULD. It shows only that the
  choice was not consequential in THIS evidence universe. It is not evidence
  that interval selection does not matter, and must not be quoted as such.""")
    return 0


if __name__ == "__main__":
    sys.exit(main())
