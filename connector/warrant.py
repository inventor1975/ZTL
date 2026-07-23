"""The warrant-form: the connector's input contract (SPEC §1).

A warrant-form is a JSON object:

    {
      "claim": "cleared & ~flagged",
      "rule":  {"id": "...", "version": "1.0.0", "hash": "<sha256hex>"},
      "atoms": [
        {"name": "cleared", "value": "T", "provenance": "...", "admissible": "yes"},
        {"name": "flagged", "value": "Z", "provenance": "...", "admissible": "yes"}
      ]
    }

This module validates the shape and produces the kernel MARKING — the
{atom_name: "T"|"F"|"Z"} dict the judge consumes — applying the fail-closed
rule. It reads `provenance` never (audit-only, SPEC §7).
"""
from __future__ import annotations

import os
import sys
from typing import Any

# the ZTL kernel lives in the repo root, one level up from connector/
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ztl import VALUES  # noqa: E402  ("T", "F", "Z")
from ztljudge import formalize as _formalize, _atoms as _formula_atoms  # noqa: E402

MARK = "Z"  # the mark / unverified / default-deny ground

# --- input bounds: DoS guard on the wire (SPEC §7 is the world; this is the pipe) ---
# The kernel's warranty grade costs O(3 ** distinct_atoms) — it scans every
# completion of the Z-marked atoms — and the claim parser is recursive. Untrusted
# warrant-forms MUST be bounded or a tiny payload hangs or crashes the judge
# (measured: 14 distinct atoms > 8s; ~1000-deep nesting -> RecursionError).
# Tighten these per-deployment if needed; nothing legitimate approaches them.
MAX_CLAIM_LEN = 1024          # characters in the claim string
MAX_ATOMS = 64                # entries in the atoms list
MAX_DISTINCT_ATOMS = 12       # atoms in the CLAIM -> 3**12 ~= 5.3e5, sub-second
MAX_NAME_LEN = 128            # characters in an atom name
MAX_PROVENANCE_LEN = 4096     # characters in an atom's provenance (audit string)


class WarrantError(ValueError):
    """The warrant-form is malformed at the STRUCTURE level (not the atom
    level — bad atom *values* are fail-closed, not rejected)."""


def _require(cond: bool, msg: str):
    if not cond:
        raise WarrantError(msg)


def validate(wf: Any) -> None:
    """Structural validation. Atom-value problems are NOT errors here — they are
    coerced to Z by `to_marking` (fail-closed). Only shape errors raise."""
    _require(isinstance(wf, dict), "warrant-form must be an object")
    claim = wf.get("claim")
    _require(isinstance(claim, str) and claim.strip(),
             "claim must be a non-empty string")
    _require(len(claim) <= MAX_CLAIM_LEN,
             f"claim too long ({len(claim)} > {MAX_CLAIM_LEN})")
    rule = wf.get("rule")
    _require(isinstance(rule, dict), "rule must be an object")
    for k in ("id", "version", "hash"):
        _require(isinstance(rule.get(k), str) and rule[k].strip(),
                 f"rule.{k} must be a non-empty string")
    atoms = wf.get("atoms")
    _require(isinstance(atoms, list), "atoms must be a list")
    _require(len(atoms) <= MAX_ATOMS,
             f"too many atoms ({len(atoms)} > {MAX_ATOMS})")
    seen = set()
    for a in atoms:
        _require(isinstance(a, dict), "each atom must be an object")
        name = a.get("name")
        _require(isinstance(name, str) and name.strip(),
                 "atom.name must be a non-empty string")
        _require(len(name) <= MAX_NAME_LEN,
                 f"atom.name too long ({len(name)} > {MAX_NAME_LEN})")
        prov = a.get("provenance")
        _require(prov is None or (isinstance(prov, str)
                 and len(prov) <= MAX_PROVENANCE_LEN),
                 f"atom.provenance too long (> {MAX_PROVENANCE_LEN})")
        _require(name not in seen, f"duplicate atom {name!r}")
        seen.add(name)
    # combinatorial + recursion guard: parse once, safely, and bound the
    # distinct-atom count that drives the 3**n grade computation.
    try:
        phi = _formalize(claim)
    except RecursionError:
        raise WarrantError("claim nesting too deep")
    n = len(_formula_atoms(phi))
    _require(n <= MAX_DISTINCT_ATOMS,
             f"too many distinct atoms in claim ({n} > {MAX_DISTINCT_ATOMS}); "
             f"grade cost is 3**n")


def to_marking(wf: Any) -> dict:
    """Produce the kernel marking, fail-closed (SPEC §1).

    For each declared atom, the effective value is its `value` ONLY when the
    value is a real T/F verdict AND `admissible == "yes"`; anything else
    (Z, unknown, missing, malformed, inadmissible) becomes Z — unverified
    ground is never waved through. Atoms named in the claim but absent from the
    list are left to the kernel's own default-deny (also Z).
    """
    validate(wf)
    marking = {}
    for a in wf["atoms"]:
        value = a.get("value")
        admissible = a.get("admissible")
        decided = value in ("T", "F")            # a real verdict, not the mark
        ok = decided and admissible == "yes"
        marking[a["name"]] = value if ok else MARK
    # sanity: every marking value is a legal kernel symbol
    assert all(v in VALUES for v in marking.values())
    return marking
