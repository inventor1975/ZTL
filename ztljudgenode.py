# -*- coding: utf-8 -*-
"""
ztljudgenode — a ZTL judge with MEMORY: one node of the (future) federated verdict
network, useful already on its own.

It gives the stateless judge (ztljudge) a persistent, auditable memory and a
time dimension:

  * atoms         — the current verdict of each atom (T/F/Z) + its provenance.
  * transitions   — an APPEND-ONLY log of every status change (Z→T, T→F, …),
                    hash-chained: each row carries prev_hash and a row_hash
                    over its canonical payload. The chain is tamper-evident —
                    no past decision can be silently rewritten (the "blockchain
                    property", without a blockchain: no mining, no consensus).
  * verdicts      — NOT stored. A verdict is a deterministic, REPRODUCIBLE
                    function of (formula + the current atom snapshot): it is
                    recomputed on demand and returned with a `verdict_hash`.
                    Two honest nodes on the same atoms and the same kernel
                    produce the same hash — the anchor of proof-of-fault (a
                    node reporting a different hash is provably wrong).

This is exactly one judge of the network: the consensus/BFT layer (deferred,
adopted from mature infra when a real consortium exists) just replicates these
nodes and agrees on the ORDER of transitions. The node stands and is testable
alone. SQLite now (local, single-writer); migrates to a shared server DB when
it becomes a service.

Run:  python3 ztljudgenode.py
"""
import hashlib
import json
import os
import sqlite3
import sys
from datetime import datetime, timezone

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ztljudge import judge, formalize, _show, _atoms                # noqa: E402
from ztl import T, F, Z, VALUES                                     # noqa: E402
from cryptography.hazmat.primitives.asymmetric.ed25519 import (     # noqa: E402
    Ed25519PrivateKey, Ed25519PublicKey)
from cryptography.hazmat.primitives.serialization import (          # noqa: E402
    Encoding, PublicFormat)
from cryptography.exceptions import InvalidSignature               # noqa: E402

GENESIS = "0" * 64


def _canon(obj) -> str:
    """A canonical, byte-stable JSON serialization (sorted keys, ASCII, no
    incidental whitespace) so a hash is reproducible across machines."""
    return json.dumps(obj, sort_keys=True, ensure_ascii=True,
                      separators=(",", ":"))


def _h(s: str) -> str:
    return hashlib.sha256(s.encode("utf-8")).hexdigest()


def _now() -> str:
    return datetime.now(timezone.utc).isoformat()


class Node:
    """One judge node with a persistent, hash-chained memory."""

    def __init__(self, db_path: str = "ztljudgenode.db", seed: bytes = None):
        # the node's signing identity (a seed gives a stable id for demos)
        self._sk = (Ed25519PrivateKey.from_private_bytes(seed) if seed
                    else Ed25519PrivateKey.generate())
        self.node_id = self._sk.public_key().public_bytes(
            Encoding.Raw, PublicFormat.Raw).hex()
        self.db = sqlite3.connect(db_path)
        self.db.execute(
            "CREATE TABLE IF NOT EXISTS atoms (name TEXT PRIMARY KEY, "
            "verdict TEXT NOT NULL, provenance TEXT, updated_at TEXT, "
            "updated_by TEXT, expires_at TEXT)")
        self.db.execute(
            "CREATE TABLE IF NOT EXISTS transitions (seq INTEGER PRIMARY KEY, "
            "ts TEXT, atom TEXT, from_v TEXT, to_v TEXT, reason TEXT, "
            "source TEXT, prev_hash TEXT, row_hash TEXT)")
        self.db.commit()

    # ---- reading current state -------------------------------------------
    def verdict_of(self, name: str):
        row = self.db.execute("SELECT verdict FROM atoms WHERE name=?",
                              (name,)).fetchone()
        return row[0] if row else None

    def _last(self):
        return self.db.execute(
            "SELECT seq, row_hash FROM transitions ORDER BY seq DESC "
            "LIMIT 1").fetchone()

    # ---- the act: change an atom's status, append to the chain -----------
    def assert_atom(self, name: str, verdict: str, reason: str = "",
                    source: str = "", ttl: float = None):
        """Record a verdict on an atom (grounding it T/F, or marking it Z).
        A change appends one hash-chained transition; a no-op is ignored.
        `ttl` (seconds) gives a grounding a shelf-life: after it lapses,
        expire_due() reverts the atom to Z — a shelf does not insure against
        the loss of its ground (ZTime, E25)."""
        if verdict not in VALUES:
            raise ValueError(f"verdict must be one of {sorted(VALUES)}")
        cur = self.verdict_of(name)
        if cur == verdict:
            return None                      # nothing changed, nothing logged
        last = self._last()
        seq = (last[0] + 1) if last else 1
        prev = last[1] if last else GENESIS
        ts = _now()
        expires = (None if (ttl is None or verdict == Z)
                   else datetime.fromisoformat(ts).timestamp() + ttl)
        expires_iso = (None if expires is None
                       else datetime.fromtimestamp(expires, timezone.utc)
                       .isoformat())
        payload = _canon({"seq": seq, "ts": ts, "atom": name, "from": cur,
                          "to": verdict, "reason": reason, "source": source,
                          "prev": prev})
        row_hash = _h(payload)
        self.db.execute(
            "INSERT INTO transitions (seq, ts, atom, from_v, to_v, reason, "
            "source, prev_hash, row_hash) VALUES (?,?,?,?,?,?,?,?,?)",
            (seq, ts, name, cur, verdict, reason, source, prev, row_hash))
        self.db.execute(
            "INSERT INTO atoms (name, verdict, provenance, updated_at, "
            "updated_by, expires_at) VALUES (?,?,?,?,?,?) ON CONFLICT(name) "
            "DO UPDATE SET verdict=excluded.verdict, "
            "provenance=excluded.provenance, updated_at=excluded.updated_at, "
            "updated_by=excluded.updated_by, expires_at=excluded.expires_at",
            (name, verdict, reason, ts, source, expires_iso))
        self.db.commit()
        return {"seq": seq, "atom": name, "from": cur, "to": verdict,
                "row_hash": row_hash}

    def expire_due(self, now: str = None):
        """Revert to Z every grounded atom whose shelf-life has lapsed by
        `now` (default: real now). Each reversion is a logged transition —
        the ground can be lost, and the ledger shows when. Returns the names
        expired."""
        now = now or _now()
        due = [r[0] for r in self.db.execute(
            "SELECT name FROM atoms WHERE expires_at IS NOT NULL AND "
            "expires_at <= ? AND verdict != ?", (now, Z)).fetchall()]
        for name in due:
            self.assert_atom(name, Z, "grounding expired", "clock")
        return due

    # ---- the verdict: reproducible, hashable, NOT stored -----------------
    def judge_claim(self, formula: str) -> dict:
        """Judge a claim against the CURRENT atom snapshot. The result is a
        deterministic function of (formula, snapshot, kernel) and carries a
        reproducible `verdict_hash` — the anchor for proof-of-fault."""
        phi = formalize(formula)
        atoms = sorted(_atoms(phi))
        marking = {a: v for a in atoms if (v := self.verdict_of(a)) is not None}
        r = judge(formula, marking)
        snapshot = {a: (self.verdict_of(a) or Z) for a in atoms}
        record = {"formula": _show(phi), "atoms": snapshot,
                  "verdict": r["verdict"], "grade": r["grade"],
                  "disposition": r["disposition"], "why": r["why"]}
        record["verdict_hash"] = _h(_canon(
            {"formula": record["formula"], "atoms": record["atoms"],
             "verdict": record["verdict"], "grade": record["grade"],
             "disposition": record["disposition"]}))
        return record

    # ---- attestation: a SIGNED verdict a peer can audit without trust -----
    def _sign(self, msg: str) -> str:
        return self._sk.sign(msg.encode()).hex()

    def attest(self, claim: str) -> dict:
        """The node's SIGNED claim about a verdict. It carries the atom
        snapshot it judged, so any auditor can re-compute and check — no trust,
        no vote. The signature makes it non-repudiable."""
        r = self.judge_claim(claim)
        body = {"node_id": self.node_id, "formula": r["formula"],
                "atoms": r["atoms"], "verdict": r["verdict"],
                "grade": r["grade"], "disposition": r["disposition"]}
        return {**body, "verdict_hash": r["verdict_hash"],
                "sig": self._sign(_canon(body))}

    def forge(self, claim: str, verdict: str, disposition: str) -> dict:
        """DEMO ONLY: a Byzantine node signs a verdict that does NOT follow
        from its own snapshot — to show audit() catches it with proof."""
        r = self.judge_claim(claim)
        body = {"node_id": self.node_id, "formula": r["formula"],
                "atoms": r["atoms"], "verdict": verdict,
                "grade": r["grade"], "disposition": disposition}
        return {**body, "verdict_hash": "(forged)",
                "sig": self._sign(_canon(body))}

    # ---- audit: the append-only history and the chain integrity ----------
    def history(self, atom: str):
        return self.db.execute(
            "SELECT seq, ts, from_v, to_v, reason, source FROM transitions "
            "WHERE atom=? ORDER BY seq", (atom,)).fetchall()

    def verify_chain(self):
        """Re-walk the log, recompute every row_hash and every link. Any
        silent edit to a past transition is detected here."""
        prev = GENESIS
        n = 0
        for row in self.db.execute(
                "SELECT seq, ts, atom, from_v, to_v, reason, source, "
                "prev_hash, row_hash FROM transitions ORDER BY seq"):
            seq, ts, atom, from_v, to_v, reason, source, prev_hash, row_hash = row
            if prev_hash != prev:
                return False, f"broken link at seq {seq}"
            payload = _canon({"seq": seq, "ts": ts, "atom": atom,
                              "from": from_v, "to": to_v, "reason": reason,
                              "source": source, "prev": prev})
            if _h(payload) != row_hash:
                return False, f"tampered row at seq {seq}"
            prev = row_hash
            n += 1
        return True, f"{n} transitions, chain intact"


# ---------------------------------------------------------------------------
def audit(att: dict) -> dict:
    """Verify a peer's signed attestation with NO trust and NO vote: check the
    signature is really the node's, then RE-COMPUTE the verdict from the atom
    snapshot the attestation carries. A mismatch is a self-contained,
    non-repudiable PROOF-OF-FAULT — the node signed a verdict that does not
    follow from its own stated atoms; anyone can re-run and see it.

    Scope: this catches a wrong VERDICT on a given snapshot (the deterministic
    layer). Agreement on the snapshot itself — which inputs are admitted — is
    the consensus layer's job, not this."""
    body = {k: att[k] for k in ("node_id", "formula", "atoms", "verdict",
                                "grade", "disposition")}
    try:
        pub = Ed25519PublicKey.from_public_bytes(bytes.fromhex(att["node_id"]))
        pub.verify(bytes.fromhex(att["sig"]), _canon(body).encode())
    except (InvalidSignature, ValueError):
        return {"result": "BAD_SIG", "node": att["node_id"][:12]}
    r = judge(att["formula"], att["atoms"])
    if att["verdict"] == r["verdict"] and att["disposition"] == r["disposition"]:
        return {"result": "CONFIRMED", "verdict": r["verdict"]}
    return {"result": "FAULT", "node": att["node_id"][:12],
            "attested": att["verdict"], "true": r["verdict"],
            "true_disposition": r["disposition"]}


def _disp(node, claim):
    r = node.judge_claim(claim)
    print(f"    {claim!r}  →  {r['disposition']:9s}  "
          f"(verdict {r['verdict']}, {r['grade']})  hash {r['verdict_hash'][:12]}…")
    return r


def main():
    print("=" * 78)
    print("ztljudgenode — a ZTL judge with memory: atoms · hash-chained "
          "transitions · reproducible verdicts")
    print("=" * 78)
    node = Node(":memory:")
    claim = "identity_check & funds_check"

    print("\n1. an access claim, funds not yet checked (funds_check = Z):")
    node.assert_atom("identity_check", T, "passport verified", "gov-api")
    r1 = _disp(node, claim)

    print("\n2. funds verified over time (Z→T) — the SAME claim, re-judged:")
    node.assert_atom("funds_check", T, "cleared by bank", "bank-api")
    r2 = _disp(node, claim)

    print("\n3. a chargeback revokes it (T→F) — status changes again:")
    node.assert_atom("funds_check", F, "chargeback detected", "bank-api")
    r3 = _disp(node, claim)

    print("\n4. the append-only history of funds_check (the 'blockchain'):")
    for seq, ts, fv, tv, reason, source in node.history("funds_check"):
        print(f"    seq {seq}: {fv or '·'} → {tv}   [{source}] {reason}")

    print("\n5. chain integrity + verdict reproducibility:")
    ok, detail = node.verify_chain()
    print(f"    verify_chain: {ok} — {detail}")
    again = node.judge_claim(claim)["verdict_hash"]
    print(f"    same state re-judged → same hash: {again == r3['verdict_hash']}")

    print("\n6. tamper detection — silently edit a past transition:")
    node.db.execute("UPDATE transitions SET reason='forged' WHERE seq=2")
    node.db.commit()
    ok2, detail2 = node.verify_chain()
    print(f"    verify_chain after edit: {ok2} — {detail2}")

    print("\n7. proof-of-fault — agree by re-computation, not by vote:")
    A = Node(":memory:", seed=b"A" * 32)
    B = Node(":memory:", seed=b"B" * 32)
    for nd in (A, B):
        nd.assert_atom("identity_check", T, "verified", "gov")
        nd.assert_atom("funds_check", T, "cleared", "bank")
    attA, attB = A.attest(claim), B.attest(claim)
    print(f"    A,B agree WITHOUT voting: same verdict_hash="
          f"{attA['verdict_hash'] == attB['verdict_hash']}  "
          f"(audit → {audit(attA)['result']}/{audit(attB)['result']})")
    liar = Node(":memory:", seed=b"F" * 32)
    liar.assert_atom("identity_check", T, "verified", "gov")
    liar.assert_atom("funds_check", T, "cleared", "bank")
    lie = liar.forge(claim, F, "REFUTED")            # true is T/EARNED
    resF = audit(lie)
    print(f"    Byzantine node signs REFUTED → audit: {resF['result']} "
          f"(attested {resF['attested']}, TRUE {resF['true']}) — signed, so "
          "non-repudiable")
    tampered = dict(attA, verdict=F)                 # edit verdict, don't re-sign
    print(f"    edit an attestation without re-signing → audit: "
          f"{audit(tampered)['result']}")

    print("\n8. expiry — a grounding has a shelf-life (ZTime live):")
    E = Node(":memory:")
    E.assert_atom("badge", T, "scanned", "reader", ttl=3600)   # 1-hour ground
    b1 = E.judge_claim("badge")["disposition"]
    expired = E.expire_due("2999-01-01T00:00:00+00:00")        # jump past shelf
    b2 = E.judge_claim("badge")["disposition"]
    print(f"    badge grounded → {b1};  shelf-life lapses → expire {expired} "
          f"→ {b2}  (the ground was lost, and the ledger shows when)")

    # honest self-check
    assert b1 == "EARNED" and expired == ["badge"] and b2 == "OPEN"
    assert r1["disposition"] == "OPEN"       # funds unverified
    assert r2["disposition"] == "EARNED"     # funds grounded
    assert r3["disposition"] == "REFUTED"    # funds refuted
    assert again == r3["verdict_hash"]       # deterministic / reproducible
    assert ok and not ok2                     # chain verifies, tamper caught
    assert attA["verdict_hash"] == attB["verdict_hash"]   # agree without voting
    assert audit(attA)["result"] == "CONFIRMED"
    assert audit(lie)["result"] == "FAULT"               # liar caught by re-run
    assert audit(tampered)["result"] == "BAD_SIG"        # unsigned edit caught
    print("\nZTLJUDGENODE GREEN — memory + hash-chained transitions + "
          "reproducible verdicts + signed attestations with proof-of-fault + "
          "expiry, over the ztljudge core.")


if __name__ == "__main__":
    main()
