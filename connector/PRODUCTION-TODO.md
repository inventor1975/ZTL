# ZTL Connector — production TODO

Deferred items to do at deployment (not needed for the connector to be complete;
the architecture is in place and tested).

## Crypto — activate quantum-resistant signatures

- [ ] Install an **audited** ML-DSA backend at deploy — **liboqs** (Open Quantum
      Safe) via `oqs` Python bindings. NOT a toy pure-python lib.
- [ ] Wire it into `connector/signer.py::_detect_mldsa` (the slot is ready; this
      is a small registration — no other change).
- [ ] Switch the default signer scheme to **`ed25519+ml-dsa-65`** (hybrid).
- Until then: Ed25519 is live and working; the hybrid scheme is defined and
  reports `unavailable` honestly. Truthful claim today: "quantum-ready,
  crypto-agile, hybrid Ed25519+ML-DSA supported" — NOT "signing ML-DSA today".

## Schema validation

- [x] `jsonschema` installed; formal validation wired into `harness.py`
      (8 warrant-forms + 8 artifacts validated).
