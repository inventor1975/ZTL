# Signing keys of the ZTL API

The ZTL API at `https://api.vitalyreznik.com` signs the verdicts it gives on `POST /cage/v1/verify`.

- **Only a 200 response carries a signed receipt.** Every other response carries none: refusals, errors
  and the rate limit. An unsigned response can be forged or suppressed in transit; treat it as "no
  verdict", never as a verdict.
- **The key signs these receipts and nothing else.** Every receipt carries `receiptVersion`
  (`ztl-receipt-1`), and that field is inside the signed bytes.

**How to verify a receipt.**

1. Take the `receipt` object without its `receiptDigest` and `signature` fields.
2. Canonicalise it (RFC 8785 JCS). The receipt holds only strings, booleans, nulls, and objects and
   arrays of these. It contains no numbers.
3. Recompute the SHA-256 of those bytes yourself and compare it with `receiptDigest`. That field is
   not signed, so never trust it unchecked.
4. Check `signature.value` (base64url, no padding) as a pure Ed25519 signature (not Ed25519ph) over the
   same bytes, with a key from the table below.

`signature.kid` is also outside the signed bytes. It is a lookup hint only: check against the full key.

**What a receipt binds.** Every field except `receiptDigest` and `signature` is signed. Among them:

- `requestDigest`: the SHA-256 of the exact request body. The caller must keep those bytes, because a
  re-serialised body will not match.
- `status`, `verdict` and `disposition`: ZTL's answer.
- `restsOn`: every row the document marks verified, refuted or defined, with that status and its ground
  exactly as the caller DECLARED them. At most 64 are listed; more are marked `truncated`, and the
  verdict may then rest on rows not listed.
- `attests`.
- `nonce`: optional, chosen by the caller. Without one, an old receipt for the same body can be shown
  again as if new.
- `issuedAt`: the signer's own clock, not a trusted time.

**The keys.** The server publishes them as a JWKS at `GET /cage/v1/keys`. This file is a second copy,
kept in the GitHub repository `inventor1975/ZTL`. That repository is a different system from the
server, with different credentials, but it has the same owner.

- Fetch this file over TLS from GitHub, not through the server.
- If the two copies disagree, believe this file and treat the disagreement as a sign of compromise.

| kid | status | Ed25519 public key (`x`, base64url) | SHA-256 of the 32 raw key bytes | from | until |
|---|---|---|---|---|---|
| `ztl-c6e5de87c91ad73b` | active | `EaaB0vUe3Fwn47EpMUwLch4s80pNC3VmyFqSqpOA01c` | `c6e5de87c91ad73b64f42bc09a38ef0c7f53af4c87ac43b8fb08f04697cb3c76` | 2026-10-10 | — |

The `kid` is `ztl-` followed by the first 16 hex digits of that SHA-256.

**What pinning protects against, and what it does not.**

- **It protects against** a key swapped into the server's JWKS response, or into anything between the
  server and you, by someone who does not hold the private key.
- **It does not protect against** whoever controls the server. The private key sits there, in a file
  readable only by the service, not in a hardware module. Such an attacker signs with the genuine key.

The remedy we provide is revocation in this file. It reaches only verifiers who fetch this file again,
so re-check it before relying on a receipt that matters.

**Retired and revoked keys.**

- **Retired.** A key replaced in the ordinary way keeps its row, with the date in `until`. Its private
  key is deleted. Its old receipts can still be checked, but the date inside a receipt is only the
  signer's claim.
- **Revoked.** A key compromised or suspected of it gets status `revoked`. Every receipt signed with it
  is then untrusted, including genuine ones made earlier, because nothing independent fixes when they
  were signed.

**What a signature means.** A valid signature shows one thing: whoever held this key signed this
receipt. If the service is the one published here and was not compromised, the receipt states ZTL's
answer for this request. That answer is: IF the grounds the document declares hold, THEN this verdict
follows by ZTL's rules. ZTL does not check the grounds, and a signature does not show they are true.
