# -*- coding: utf-8 -*-
"""
ztlnode — a ZTL judge with MEMORY: one node of the (future) federated verdict
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

Run:  python3 ztlnode.py
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

    def __init__(self, db_path: str = "ztlnode.db"):
        self.db = sqlite3.connect(db_path)
        self.db.execute(
            "CREATE TABLE IF NOT EXISTS atoms (name TEXT PRIMARY KEY, "
            "verdict TEXT NOT NULL, provenance TEXT, updated_at TEXT, "
            "updated_by TEXT)")
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
                    source: str = ""):
        """Record a verdict on an atom (grounding it T/F, or marking it Z).
        A change appends one hash-chained transition; a no-op is ignored."""
        if verdict not in VALUES:
            raise ValueError(f"verdict must be one of {sorted(VALUES)}")
        cur = self.verdict_of(name)
        if cur == verdict:
            return None                      # nothing changed, nothing logged
        last = self._last()
        seq = (last[0] + 1) if last else 1
        prev = last[1] if last else GENESIS
        ts = _now()
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
            "updated_by) VALUES (?,?,?,?,?) ON CONFLICT(name) DO UPDATE SET "
            "verdict=excluded.verdict, provenance=excluded.provenance, "
            "updated_at=excluded.updated_at, updated_by=excluded.updated_by",
            (name, verdict, reason, ts, source))
        self.db.commit()
        return {"seq": seq, "atom": name, "from": cur, "to": verdict,
                "row_hash": row_hash}

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
def _disp(node, claim):
    r = node.judge_claim(claim)
    print(f"    {claim!r}  →  {r['disposition']:9s}  "
          f"(verdict {r['verdict']}, {r['grade']})  hash {r['verdict_hash'][:12]}…")
    return r


def main():
    print("=" * 78)
    print("ztlnode — a ZTL judge with memory: atoms · hash-chained "
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

    # honest self-check
    assert r1["disposition"] == "OPEN"       # funds unverified
    assert r2["disposition"] == "EARNED"     # funds grounded
    assert r3["disposition"] == "REFUTED"    # funds refuted
    assert again == r3["verdict_hash"]       # deterministic / reproducible
    assert ok and not ok2                     # chain verifies, tamper caught
    print("\nZTLNODE GREEN — memory + hash-chained transitions + reproducible, "
          "hashable verdicts, over the ztljudge core.")


if __name__ == "__main__":
    main()
