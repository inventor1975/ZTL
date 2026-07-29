# -*- coding: utf-8 -*-
"""Generate the OIC interface-freeze conformance fixtures from LIVE kernel runs.

Every fixture here is produced by calling the pinned kernel and recording what
it actually returned. Nothing is hand-written from expectation. Where the work
order asks for a state the kernel cannot reach, the fixture is emitted with
status NOT_REACHABLE and the reason, rather than a fabricated example.

Usage:  python3 inventory/oic_fixtures.py <outdir>
"""
import hashlib
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import ztljudge as K          # noqa: E402
import zverify as V           # noqa: E402

# (case id, formula, marking, note)
REACHABLE = [
    ("earned-hereditary", "p", {"p": "T"},
     "grounded outright: the verdict cannot move under any further verification"),
    ("refuted", "p", {"p": "F"},
     "grounded false"),
    ("refuted-despite-marks", "p & q", {"p": "F", "q": "Z"},
     "false regardless of the unverified atom — marks do not matter here"),
    ("on-credit-sound", "(~p) -> (q -> q)", {"p": "Z", "q": "Z"},
     "TRUE ON CREDIT, sound: never lies about the present marking, but may "
     "stall under refinement. This is the E12 cell."),
    ("on-credit-until-verification", "(b -> a) -> (b = c)",
     {"a": "F", "b": "Z", "c": "T"},
     "TRUE ON CREDIT, weakest grade: the verdict rides the unverified atom "
     "and can die when it resolves"),
    ("open-with-raw-f", "p & q", {"p": "T", "q": "Z"},
     "THE TRAP: raw verdict is F (default deny) while the disposition is OPEN. "
     "An adapter reading `verdict` alone converts 'not yet established' into "
     "'established false' and breaks OIC invariant I-04."),
    ("open-with-raw-z", "p", {"p": "Z"},
     "bare unverified atom: Z survives only here; any operator collapses it"),
    ("open-negated-mark", "~p", {"p": "Z"},
     "negation of a mark: raw F, disposition OPEN — nothing is established"),
    ("nonempty-unverified", "p & (q | r)", {"p": "T", "q": "Z", "r": "Z"},
     "the unverified list names the exact blocking atoms for missing_inputs"),
    ("monotone-refinement", "p & q", {"p": "T", "q": "T"},
     "the same formula as open-with-raw-f after one tick (q: Z -> T): a tick "
     "is the arrival of ground"),
    ("contradiction", "p & ~p", {"p": "T"},
     "self-contradictory formula on grounded input"),
    ("greedy-collapse", "p | q", {"p": "Z", "q": "Z"},
     "no compound formula ever carries Z: the mark collapses under any operator"),
]

# States the work order asks for that the kernel cannot produce.
NOT_REACHABLE = [
    ("earned-sound",
     "EARNED requires grade `hereditary` by construction. A verdict T that is "
     "only `sound` is classified ON CREDIT, not EARNED — see fixture "
     "on-credit-sound. Searched exhaustively over the formula pool."),
    ("earned-until-verification",
     "Same reason: a non-hereditary T is ON CREDIT. See "
     "on-credit-until-verification."),
    ("open-with-raw-t",
     "OPEN never carries raw verdict T. A T verdict is either EARNED "
     "(hereditary) or ON CREDIT (not hereditary). Exhaustive search over the "
     "pool found no counterexample; if OIC needs this state it does not exist "
     "and no envelope rule should depend on it."),
]


def run(formula, marking):
    """One live kernel call, recorded verbatim."""
    r = K.judge(formula, marking)
    phi = K.formalize(formula)
    # zverify uses a DIFFERENT mark dialect: 'M', not 'Z'. Passing 'Z' makes it
    # silently answer "hereditary" for everything. Recorded here so a consumer
    # never repeats the mistake.
    mark_dialect = {k: ("M" if v == "Z" else v) for k, v in marking.items()}
    return {
        "input": {"formula": formula, "marking": marking},
        "raw_output": {
            "formula": r["formula"],
            "verdict": r["verdict"],
            "grade": r["grade"],
            "disposition": r["disposition"],
            "unverified": r["unverified"],
            "why": r["why"],
        },
        "cross_check": {
            "zverify_grade_with_M_dialect": V.grade(phi, mark_dialect),
            "zverify_grade_if_Z_passed_by_mistake": V.grade(phi, marking),
            "note": ("zverify.grade expects 'M' for a mark. Passing 'Z' returns "
                     "a wrong grade SILENTLY. judge() accepts 'Z' and converts "
                     "internally; prefer judge()."),
        },
        "recomputation": {
            "deterministic": True,
            "depends_on": sorted(marking.keys()),
            "recompute_when": (
                ["any atom in unverified is verified or expires"]
                if r["unverified"] else
                ["formula change", "epoch change", "expiry of any ground atom"]
            ),
        },
    }


def digest(obj):
    return hashlib.sha256(
        json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def main(outdir):
    os.makedirs(outdir, exist_ok=True)
    index, sums = [], []
    for cid, f, m, note in REACHABLE:
        body = run(f, m)
        body["case_id"] = cid
        body["note"] = note
        body["status"] = "REACHABLE"
        body["kernel"] = {"entry": "ztljudge.judge", "source": "live run"}
        body["fixture_sha256"] = digest({k: v for k, v in body.items()
                                         if k != "fixture_sha256"})
        path = os.path.join(outdir, cid + ".json")
        with open(path, "w") as fp:
            json.dump(body, fp, indent=2, sort_keys=True)
            fp.write("\n")
        with open(path, "rb") as fp:
            sums.append((hashlib.sha256(fp.read()).hexdigest(), cid + ".json"))
        index.append({"case_id": cid, "status": "REACHABLE",
                      "disposition": body["raw_output"]["disposition"],
                      "grade": body["raw_output"]["grade"],
                      "verdict": body["raw_output"]["verdict"]})
    for cid, reason in NOT_REACHABLE:
        body = {"case_id": cid, "status": "NOT_REACHABLE", "reason": reason,
                "input": None, "raw_output": None}
        body["fixture_sha256"] = digest({k: v for k, v in body.items()
                                         if k != "fixture_sha256"})
        path = os.path.join(outdir, cid + ".json")
        with open(path, "w") as fp:
            json.dump(body, fp, indent=2, sort_keys=True)
            fp.write("\n")
        with open(path, "rb") as fp:
            sums.append((hashlib.sha256(fp.read()).hexdigest(), cid + ".json"))
        index.append({"case_id": cid, "status": "NOT_REACHABLE"})

    with open(os.path.join(outdir, "INDEX.json"), "w") as fp:
        json.dump({"generated_by": "inventory/oic_fixtures.py",
                   "kernel_entry": "ztljudge.judge",
                   "reachable": len(REACHABLE),
                   "not_reachable": len(NOT_REACHABLE),
                   "cases": index}, fp, indent=2, sort_keys=True)
        fp.write("\n")
    with open(os.path.join(outdir, "INDEX.json"), "rb") as fp:
        sums.append((hashlib.sha256(fp.read()).hexdigest(), "INDEX.json"))

    with open(os.path.join(outdir, "SHA256SUMS"), "w") as fp:
        for h, n in sorted(sums, key=lambda x: x[1]):
            fp.write(f"{h}  {n}\n")

    print(f"{len(REACHABLE)} reachable + {len(NOT_REACHABLE)} not-reachable "
          f"fixtures written to {outdir}")
    for c in index:
        s = c.get("disposition", "—")
        print(f"  {c['case_id']:32s} {c['status']:15s} {s}")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "oic-fixtures")
