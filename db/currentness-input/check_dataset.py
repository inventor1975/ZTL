# -*- coding: utf-8 -*-
"""Is this body of records adequate for the currentness measurement?

Answerable BEFORE access is negotiated, and answerable by the record holder
without sending anything to us. Point it at a dataset described by
``currentness-events-v0.1.schema.json`` and it reports, condition by condition,
what the measurement would and would not be entitled to say.

It refuses rather than degrades. A dataset that cannot support the measurement
produces a refusal that names the missing condition, not a number with a
caveat attached — the number is what gets quoted, and the caveat is what gets
dropped.

Run:  python3 db/currentness-input/check_dataset.py <dataset.json>
"""
from __future__ import annotations

import json
import sys
from datetime import datetime
from pathlib import Path

SCHEMA_VERSION = "CURRENTNESS-INPUT-v0.1"


def _t(value: str) -> datetime:
    return datetime.fromisoformat(value.replace("Z", "+00:00"))


def conditions(d: dict) -> list[dict]:
    """Each condition names what it protects, so a FAIL is actionable."""
    out: list[dict] = []

    def check(cid, holds, protects, detail=""):
        out.append({"id": cid, "status": "HOLDS" if holds else "FAILS",
                    "protects": protects, "detail": detail})

    changes = d.get("changes", [])
    acts = d.get("acts", [])
    deps = d.get("dependencies", [])

    exact = [c for c in changes if c.get("effective_at_precision", "EXACT") == "EXACT"]
    check("A1-both-timestamps", bool(changes) and all(
              c.get("effective_at") and c.get("recorded_at") for c in changes),
          "lag is computable at all",
          f"{len(changes)} changes")
    check("A2-effective-time-known", len(exact) == len(changes) and bool(changes),
          "lag is not silently inferred from the recording time",
          f"{len(exact)}/{len(changes)} changes carry an EXACT effective time")

    lagged = [c for c in exact if c.get("recorded_at") and c.get("effective_at")
              and _t(c["recorded_at"]) > _t(c["effective_at"])]
    check("A3-a-window-exists", bool(lagged),
          "the run is not vacuous",
          f"{len(lagged)} changes were recorded after they took effect")

    dep_conclusions = {x["conclusion_id"] for x in deps}
    orphan = [a for a in acts if a["conclusion_id"] not in dep_conclusions]
    check("A4-acts-attributable", bool(acts) and not orphan,
          "exposure can be attributed to a basis",
          f"{len(orphan)} acts rest on a conclusion with no recorded dependency")

    check("A5-acts-typed", bool(acts) and all(a.get("act_type") for a in acts),
          "the 'number and TYPE of acts' finding is supported, not just the count")

    req = d.get("requirement", {})
    check("A6-requirement-is-theirs", bool(req.get("declared_by")) and bool(req.get("statement")),
          "'blind' is defined by the institution, not chosen by the analyst",
          f"declared_by={req.get('declared_by')!r}")

    completeness = d.get("scope", {}).get("completeness")
    check("A7-closure-stated", completeness in {"COMPLETE", "COMPLETE_FOR_LISTED_BASES"},
          "an absent change event means 'no change', not 'not recorded'",
          f"completeness={completeness!r}")

    ordering = d.get("ordering") or {}
    clock = ordering.get("clock", "SINGLE_TRUSTED")
    skew = ordering.get("max_skew_seconds")
    lags = [( _t(c["recorded_at"]) - _t(c["effective_at"]) ).total_seconds() for c in lagged]
    smallest = min(lags) if lags else None
    separable = clock != "MULTIPLE_UNSYNCHRONISED" or (
        skew is not None and smallest is not None and skew < smallest)
    check("A8-lag-separable-from-skew", separable,
          "the measured lag is not clock skew wearing a lag's clothes",
          f"clock={clock}, max_skew={skew}, smallest observed lag={smallest}")

    return out


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print(__doc__)
        return 2
    d = json.loads(Path(argv[1]).read_text(encoding="utf-8"))

    print("=" * 74)
    print("CURRENTNESS DATASET ADEQUACY — v0.1")
    print("=" * 74)
    if d.get("schema_version") != SCHEMA_VERSION:
        print(f"  REFUSED: schema_version is {d.get('schema_version')!r}, not {SCHEMA_VERSION!r}")
        return 1

    results = conditions(d)
    for r in results:
        mark = "ok  " if r["status"] == "HOLDS" else "FAIL"
        print(f"  [{mark}] {r['id']:<26} {r['protects']}")
        if r["detail"]:
            print(f"         {r['detail']}")

    failed = [r for r in results if r["status"] == "FAILS"]
    hard = [r for r in failed if r["id"] in
            {"A1-both-timestamps", "A2-effective-time-known", "A4-acts-attributable",
             "A6-requirement-is-theirs", "A8-lag-separable-from-skew"}]

    print()
    if hard:
        print("  VERDICT: INADEQUATE — the measurement must not be run.")
        for r in hard:
            print(f"    missing: {r['id']} — {r['protects']}")
        verdict = "INADEQUATE"
    elif failed:
        print("  VERDICT: ADEQUATE WITH STATED LIMITS — the run may proceed and")
        print("  must carry these limits in its own output, not in a footnote:")
        for r in failed:
            print(f"    limit: {r['id']} — {r['protects']}")
        verdict = "ADEQUATE_WITH_LIMITS"
    else:
        print("  VERDICT: ADEQUATE for the currentness measurement as specified.")
        verdict = "ADEQUATE"

    print("""
  WHAT ADEQUACY IS NOT. It says the measurement can be computed from these
  records. It says nothing about whether the result generalises beyond them,
  and nothing about permission to use them. Both are decisions for the
  record holder and for counsel, and neither is a property of the data.""")
    Path("adequacy-report.json").write_text(
        json.dumps({"verdict": verdict, "conditions": results}, indent=2) + "\n",
        encoding="utf-8")
    print("\n  written: adequacy-report.json")
    return 0 if verdict != "INADEQUATE" else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
