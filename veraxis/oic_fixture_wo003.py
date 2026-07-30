# -*- coding: utf-8 -*-
"""OIC-WO-003 Phase 1: the earned-hereditary-nonempty-unverified fixture.

One LIVE kernel run, recorded verbatim, with full provenance: the pinned
repository and commit, both hash projections exactly as defined by the OIC
semantic-conformance rules (SC-WA-002), and a recomputation command a stranger
can run from a clean clone.

The fixture witnesses the measured fact that closed the PR #16 mapping row:
EARNED / hereditary MAY carry a non-empty `unverified` list — the marks are
informational (the verdict does not read them), 61 of 294 census cases.

Usage:  python3 veraxis/oic_fixture_wo003.py <outdir>
"""
import hashlib
import json
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
import ztljudge as K          # noqa: E402
import zverify as V           # noqa: E402

CASE_ID = "earned-hereditary-nonempty-unverified"
FORMULA = "p | q"
MARKING = {"p": "T", "q": "Z"}
REPOSITORY = "https://github.com/inventor1975/ZTL"
SIGNED_TAG = "veraxis-ztl-input-v0.2-signed"

# NOTE ON THE PIN. OIC-WO-003 asked this fixture to record the v0.1 pin
# e819dec7. MEASURED: that commit predates ztljudge.judge entirely (judge()
# was added in 25510dd and renamed in c858429, both later), and
# verify_fixtures.py against a clean e819dec7 worktree exits 2 with
# "No module named 'ztljudge'". A fixture pinned there would carry a
# recomputation command that provably fails. This fixture therefore pins the
# commit it was actually produced from, under the signed tag above; the
# deviation is recorded in CONFORMANCE-v0.2.md and in the PR review.

# The output the work order requires. If the kernel ever returns anything else,
# this generator must FAIL, not write a fixture.
REQUIRED = {"disposition": "EARNED", "grade": "hereditary",
            "verdict": "T", "unverified": ["q"]}


def compact(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=False).encode("utf-8")


def digest(obj):
    # same discipline as veraxis/oic_fixtures.py (v0.1)
    return hashlib.sha256(
        json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def pinned_commit():
    return subprocess.check_output(
        ["git", "-C", ROOT, "rev-parse", "HEAD"], text=True).strip()


def main(outdir):
    r = K.judge(FORMULA, MARKING)
    for k, want in REQUIRED.items():
        if r[k] != want:
            sys.exit(f"KERNEL DRIFT: {k} = {r[k]!r}, work order requires {want!r}")

    phi = K.formalize(FORMULA)
    mark_dialect = {k: ("M" if v == "Z" else v) for k, v in MARKING.items()}
    commit = pinned_commit()

    # The two projections, byte-for-byte as OIC defines them
    # (tests/contract/semantic_conformance.py, SC-WA-002).
    formula_hash = "sha384:" + hashlib.sha384(
        r["formula"].encode("utf-8")).hexdigest()
    output_hash = "sha256:" + hashlib.sha256(compact({
        "kernel_rendered_formula": r["formula"],
        "disposition": r["disposition"],
        "raw_verdict": r["verdict"],
        "warranty_grade": r["grade"],
        "unverified_ground_ids": list(r["unverified"]),
    })).hexdigest()

    body = {
        "case_id": CASE_ID,
        "status": "REACHABLE",
        "input": {"formula": FORMULA, "marking": MARKING},
        "input_sha256": digest({"formula": FORMULA, "marking": MARKING}),
        "raw_output": {
            "formula": r["formula"],
            "verdict": r["verdict"],
            "grade": r["grade"],
            "disposition": r["disposition"],
            "unverified": r["unverified"],
            "why": r["why"],
        },
        "kernel": {
            "entry": "ztljudge.judge",
            "source": "live run",
            "repository": REPOSITORY,
            "pinned_commit": commit,
            "signed_tag": SIGNED_TAG,
        },
        "oic_derivation": {
            "dependency_ids": sorted(k for k, v in MARKING.items()
                                     if v in ("T", "F")),
            "rule": ("dependency_ids = every VERIFIED atom (T or F) in the "
                     "evaluated formula; over-approximation, no minimality "
                     "claim (kernel-profile ztl-v0.1)"),
            "disjoint_from_unverified": True,
        },
        "projections": {
            "definition": "tests/contract/semantic_conformance.py (SC-WA-002)",
            "formula_hash": formula_hash,
            "output_hash": output_hash,
        },
        "note": (
            "EARNED + hereditary with a NON-EMPTY unverified list. The atom q is "
            "INFORMATIONAL for this conclusion: the verdict is carried entirely "
            "by p, and the kernel's own why-string states that the unverified do "
            "not matter. Kernel census: 61 of 294 cases behave this way. A "
            "mapping that keys EARNED on `unverified: empty` misroutes all of "
            "them to a procedural block."
        ),
        "cross_check": {
            "zverify_grade_with_M_dialect": V.grade(phi, mark_dialect),
            "zverify_grade_if_Z_passed_by_mistake": V.grade(phi, MARKING),
            "note": ("zverify.grade expects 'M' for a mark. Passing 'Z' returns "
                     "a wrong grade SILENTLY. judge() accepts 'Z' and converts "
                     "internally; prefer judge()."),
        },
        "recomputation": {
            "deterministic": True,
            "depends_on": sorted(MARKING.keys()),
            "recompute_when": ["any atom in unverified is verified or expires"],
            "command": (
                "git clone {repo}.git ztl-conformance && "
                "cd ztl-conformance && git checkout {commit} && "
                "python3 -c \"import json, ztljudge; print(json.dumps("
                "ztljudge.judge('p | q', {{'p': 'T', 'q': 'Z'}}), "
                "sort_keys=True))\""
            ).format(repo=REPOSITORY, commit=commit),
        },
    }
    body["fixture_sha256"] = digest({k: v for k, v in body.items()
                                     if k != "fixture_sha256"})

    os.makedirs(outdir, exist_ok=True)
    path = os.path.join(outdir, CASE_ID + ".json")
    with open(path, "w") as fp:
        json.dump(body, fp, indent=2, sort_keys=True)
        fp.write("\n")
    print(f"written {path}")
    print(f"  pinned_commit  {commit}")
    print(f"  formula_hash   {formula_hash}")
    print(f"  output_hash    {output_hash}")
    print(f"  fixture_sha256 {body['fixture_sha256']}")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "oic-fixtures-wo003")
