"""Canonicalization + hashing for the ZTL Connector.

The verdict artifact binds to its inputs by a hash, and that hash must be
reproducible across languages and machines — otherwise a consumer cannot
independently verify a verdict (SPEC §3, §4). We fix RFC 8785 (JCS) as the
canonical form.

NOTE (honest scope): this is an RFC 8785 *subset*. Warrant-forms and verdict
artifacts contain no JSON numbers (versions and hashes are strings, values are
the enums "T"/"F"/"Z"), so the hard part of JCS — ES6 number serialization — is
never exercised. Keys are sorted, the encoding is UTF-8 (so Arabic or any
non-ASCII provenance hashes stably), whitespace is stripped, and string escaping
is standard JSON. If JSON numbers are ever introduced, swap in a full JCS
implementation here — the rest of the connector is unaffected.
"""
from __future__ import annotations

import hashlib
import json
from typing import Any


def canonicalize(obj: Any) -> str:
    """RFC 8785 (JCS) subset: sorted keys, UTF-8, no incidental whitespace."""
    return json.dumps(
        obj,
        sort_keys=True,
        ensure_ascii=False,      # JCS mandates UTF-8, not \uXXXX escapes
        separators=(",", ":"),
        allow_nan=False,         # NaN/Infinity are not valid JCS
    )


def sha384_hex(obj: Any) -> str:
    """Canonicalize then SHA-384 (the connector's hash, SPEC §3)."""
    return hashlib.sha384(canonicalize(obj).encode("utf-8")).hexdigest()


def sha256_hex(obj: Any) -> str:
    """SHA-256 over the canonical form — used for rule_hash / fixture pins."""
    return hashlib.sha256(canonicalize(obj).encode("utf-8")).hexdigest()
