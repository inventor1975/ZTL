# Signing keys of the ZTL API

The ZTL API at `https://api.vitalyreznik.com` signs the verdicts it gives on `POST /cage/v1/verify`
(Ed25519 over RFC 8785 canonical JSON; the receipt's `receiptDigest` is the SHA-256 of the same bytes).
The server also publishes its keys at `GET /cage/v1/keys`. **This file is the second, independent copy:**
a verifier should pin the key from here, not only from the server, so that a compromised server cannot
substitute its own key together with its own signatures.

| kid | Ed25519 public key (`x`, base64url) | SHA-256 of the raw public key | in use since |
|---|---|---|---|
| `ztl-c6e5de87c91ad73b` | `EaaB0vUe3Fwn47EpMUwLch4s80pNC3VmyFqSqpOA01c` | `c6e5de87c91ad73b64f42bc09a38ef0c7f53af4c87ac43b8fb08f04697cb3c76` | 2026-10-10 |

The `kid` is `ztl-` followed by the first 16 hex digits of that SHA-256, so a receipt names the key it
was signed with. When a key is replaced, the old line stays here, marked retired with its date, so
that receipts signed before the change can still be verified.

**What a signature attests.** That the verdict follows, by ZTL, from the grounds the submitted
document declares. The grounds themselves are the caller's statements; ZTL does not verify them. The
signed receipt lists them under `restsOn` and says so under `attests`.
