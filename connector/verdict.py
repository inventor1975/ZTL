"""The reference evaluator + verdict artifact (SPEC §2, §3, §4).

`judge_warrant` is the ONE reference: it turns a warrant-form into a signed,
re-computable verdict artifact by delegating the verdict to the ZTL kernel
(`ztljudge.judge`) — it never re-implements the verdict (the layering invariant).

`verify_artifact` re-computes the verdict from the warrant-form and checks the
digest and signature — the offline, protocol-free verification of SPEC §4.
"""
from __future__ import annotations

import os
import sys
from typing import Optional

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import ztljudge  # noqa: E402  — the one kernel; we DELEGATE, never re-implement
from connector.canon import sha384_hex  # noqa: E402
from connector.signer import Signer, verify_signature  # noqa: E402
from connector.warrant import to_marking, validate  # noqa: E402

KERNEL_VERSION = "ztljudge-v0.1"
CONNECTOR_VERSION = "0.1"

# the artifact fields the signature covers (everything but the signature itself)
_BODY_FIELDS = ("input_digest", "rule", "kernel_version",
                "verdict", "grade", "disposition", "why", "unverified")


# ---- Application note (NON-NORMATIVE — the connector enforces none of this) ----
# The connector is domain-agnostic: its unit is a key that renders verdicts, and
# it neither knows nor mandates how many judges an entity has. Consumers compose
# it however their domain needs (MindReef uses a single warrant gate; a pure
# verifier uses one judge; etc.).
#
# As ONE such application pattern, a country / governance profile pairs TWO
# judges per person — a cold "law" judge (sovereign voice, rarely used) and a
# hot "executor" judge (daily acts, wired to the consuming protocol). That
# pairing is worth enforcing THERE, at enrollment in the governance profile,
# because it keeps two things from collapsing into one seat: the separation of
# law-making from law-applying, and the hygiene of a cold sovereign key vs a hot
# operational key. It is a governance-layer invariant, deliberately NOT a rule of
# this universal connector.
# --------------------------------------------------------------------------------


def _kernel_verdict(wf: dict) -> dict:
    """Delegate to the kernel and lift out the SPEC §2 fields."""
    marking = to_marking(wf)
    r = ztljudge.judge(wf["claim"], marking)
    return {
        "verdict": r["verdict"],
        "grade": r["grade"],
        "disposition": r["disposition"],
        "why": r["why"],
        "unverified": r["unverified"],
    }


def _body(wf: dict, kv: dict) -> dict:
    return {
        "input_digest": sha384_hex(
            {"claim": wf["claim"], "rule": wf["rule"], "atoms": wf["atoms"]}),
        "rule": wf["rule"],
        "kernel_version": KERNEL_VERSION,
        **kv,
    }


def judge_warrant(wf: dict, signer: Optional[Signer] = None) -> dict:
    """Warrant-form -> signed verdict artifact. If no signer is given, the
    artifact carries no signature (still re-computable — trust is in §4)."""
    validate(wf)
    kv = _kernel_verdict(wf)
    body = _body(wf, kv)
    if signer is not None:
        from connector.canon import canonicalize
        body["signature"] = signer.sign(canonicalize(body).encode("utf-8"))
    return body


def verify_artifact(artifact: dict, wf: dict) -> dict:
    """Independently verify an artifact against the warrant-form that produced
    it (SPEC §4). Returns a report; `ok` is the conjunction of all checks.

    No protocol server is contacted — reference kernel + artifact + warrant-form
    suffice. This is the anti-monopoly property in code (SPEC §5.2)."""
    from connector.canon import canonicalize

    checks = {}

    # 1. digest binds the artifact to these exact inputs
    expected_digest = sha384_hex(
        {"claim": wf["claim"], "rule": wf["rule"], "atoms": wf["atoms"]})
    checks["digest_matches"] = artifact.get("input_digest") == expected_digest

    # 2. re-compute the verdict from the warrant-form; it must match
    recomputed = _kernel_verdict(wf)
    checks["verdict_matches"] = all(
        artifact.get(k) == recomputed[k]
        for k in ("verdict", "grade", "disposition", "unverified"))

    # 3. signature (if present) vouches for the signer over the exact body
    sig = artifact.get("signature")
    if sig is None:
        checks["signature_present"] = False
    else:
        body = {k: artifact[k] for k in _BODY_FIELDS if k in artifact}
        checks["signature_present"] = True
        checks["signature_valid"] = verify_signature(
            sig, canonicalize(body).encode("utf-8"))

    ok = checks["digest_matches"] and checks["verdict_matches"] and (
        sig is None or checks.get("signature_valid", False))
    return {"ok": ok, "checks": checks, "recomputed": recomputed}
