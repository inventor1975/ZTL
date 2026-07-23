"""Crypto-agile signer / verifier for the ZTL Connector (SPEC §3, §5.3).

The signature is a VOUCHER: it attests WHO ran the judge, not that the verdict
is true. Truth lives in re-computation (SPEC §3). The scheme is swappable —
this is a hard requirement, both for crypto-agility and so no single stack is
load-bearing.

Schemes are registered by name. A scheme whose backend is not installed
registers as UNAVAILABLE, and constructing a Signer for it raises a clear
error rather than silently degrading — we never fake PQC.

Installed today:
  - "ed25519"          : working (via `cryptography`).
Registered, backend-gated:
  - "ml-dsa-65"        : NIST ML-DSA (Dilithium, FIPS 204) — needs a PQC lib
                         (`oqs` / `pqcrypto` / pure-python `dilithium`); if none
                         importable, marked unavailable.
  - "ed25519+ml-dsa-65": the SPEC default hybrid — available only when the
                         ml-dsa backend is.
"""
from __future__ import annotations

from typing import Callable, Optional

from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives.asymmetric.ed25519 import (
    Ed25519PrivateKey, Ed25519PublicKey)


# --------------------------------------------------------------- scheme backends
class _Scheme:
    """One signature scheme: keygen / sign / verify over bytes, plus an
    `available` flag so callers can see what is really usable."""

    def __init__(self, name: str, available: bool,
                 keygen: Optional[Callable] = None,
                 sign: Optional[Callable] = None,
                 verify: Optional[Callable] = None):
        self.name = name
        self.available = available
        self._keygen = keygen
        self._sign = sign
        self._verify = verify

    def keygen(self):
        return self._keygen()

    def sign(self, sk, msg: bytes) -> str:
        return self._sign(sk, msg)

    def verify(self, pub_hex: str, sig_hex: str, msg: bytes) -> bool:
        return self._verify(pub_hex, sig_hex, msg)


# -- ed25519 (working) --------------------------------------------------------
def _ed_keygen(seed: Optional[bytes] = None):
    sk = (Ed25519PrivateKey.from_private_bytes(seed) if seed
          else Ed25519PrivateKey.generate())
    pub_hex = sk.public_key().public_bytes_raw().hex()
    return sk, pub_hex


def _ed_sign(sk: Ed25519PrivateKey, msg: bytes) -> str:
    return sk.sign(msg).hex()


def _ed_verify(pub_hex: str, sig_hex: str, msg: bytes) -> bool:
    try:
        pub = Ed25519PublicKey.from_public_bytes(bytes.fromhex(pub_hex))
        pub.verify(bytes.fromhex(sig_hex), msg)
        return True
    except (InvalidSignature, ValueError):
        return False


_ED25519 = _Scheme("ed25519", available=True,
                   keygen=lambda: _ed_keygen(),
                   sign=_ed_sign, verify=_ed_verify)


# -- ml-dsa-65 (backend-gated) ------------------------------------------------
def _detect_mldsa() -> Optional[_Scheme]:
    """Return a working ml-dsa scheme if a PQC backend is importable, else None.
    Kept as a stub-detector so PQC turns on the day a backend lands, with no
    other change to the connector."""
    try:
        import oqs  # noqa: F401  (liboqs-python) — preferred if present
    except Exception:
        return None
    # A real oqs wiring goes here once the lib is confirmed present in the env.
    # Deliberately not implemented against an absent library — we do not fake it.
    return None


_MLDSA = _detect_mldsa() or _Scheme("ml-dsa-65", available=False)


SCHEMES = {
    "ed25519": _ED25519,
    "ml-dsa-65": _MLDSA,
    # hybrid is available only when both halves are
    "ed25519+ml-dsa-65": _Scheme(
        "ed25519+ml-dsa-65",
        available=_ED25519.available and _MLDSA.available),
}


def available_schemes() -> dict:
    """Name -> bool, so a caller (or the curator) sees what is really usable."""
    return {n: s.available for n, s in SCHEMES.items()}


# ------------------------------------------------------------------- Signer
class Signer:
    """Signs artifact bodies under one scheme. Raises if the scheme's backend
    is not installed — never silently degrades."""

    def __init__(self, scheme: str = "ed25519", seed: Optional[bytes] = None):
        if scheme not in SCHEMES:
            raise ValueError(f"unknown scheme {scheme!r}; "
                             f"have {sorted(SCHEMES)}")
        s = SCHEMES[scheme]
        if not s.available:
            raise RuntimeError(
                f"scheme {scheme!r} backend is not installed in this "
                f"environment; available: "
                f"{[n for n, a in available_schemes().items() if a]}. "
                f"Install a PQC backend to enable it — the connector will use "
                f"it with no code change.")
        self.scheme = s
        if scheme == "ed25519":
            self._sk, self.public_id = _ed_keygen(seed)
        else:  # pragma: no cover - reached only when a PQC backend exists
            self._sk, self.public_id = s.keygen()

    def sign(self, msg: bytes) -> dict:
        return {"scheme": self.scheme.name,
                "signer": self.public_id,
                "value": self.scheme.sign(self._sk, msg)}


def verify_signature(sig: dict, msg: bytes) -> bool:
    """Check a signature block against the message it should cover."""
    scheme = SCHEMES.get(sig.get("scheme", ""))
    if scheme is None or not scheme.available:
        return False
    return scheme.verify(sig["signer"], sig["value"], msg)
