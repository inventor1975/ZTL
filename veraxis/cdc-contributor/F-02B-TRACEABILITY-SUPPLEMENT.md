# F-02B-TRACEABILITY-SUPPLEMENT — historical artifact byte-binding

From: Vitaly Reznik (`inventor1975`), integration owner for F.
Date: 2026-08-10.
Scope: closes the F-02B traceability items **only with existing historical
artifacts** from the reviewed ZTL repository history. No new execution:
`tests_executed = 0`; `historical_measurements_reexecuted = false`;
observation mode throughout = `ARTIFACT_INSPECTION` (paths, git identities,
SHA-256 over exact bytes). No retrospective reconstruction was performed.

Repository under review: `inventor1975/ZTL`, branch `master`, reviewed at
HEAD `973f9eba2dfe410efdadad132ce2348d3875e302` (the A–E freeze commit).
All "directory unchanged" statements are `git diff <commit>..HEAD -- <path>`
= empty.

Challenge records F02B-01 / F02B-02 / F02B-05 are **PRESERVED** as capability
/ evidence ceilings (honest limitations, future release work). Nothing was
executed to close them.

---

## B-1. Phase-A raw result bundles — FOUND, byte-bound

**Unmutated arm** — commit `d5bd9e172d9dac0eae893c13a4f9ebfbc545f33f`
(tree `3c03c42239fffbf6554670a2b8624500c480176e`, 2026-08-09, "Phase A
unmutated retrospective result bundle (immutable, pre-disclosure)").
Path `veraxis/judge-experiment/phase-a/` (members: result doc,
`bundle-manifest.json`, `clwr/` 37 records, `markings/` 37 records).
Directory unchanged from that commit to reviewed HEAD.

| Member | SHA-256 |
|---|---|
| `00-PHASE-A-UNMUTATED-RESULT.json` | `83e125caaab1580e29cabf5d7806755eb9e63515ce648e438fa3231521025e1f` |
| `bundle-manifest.json` (per-member hash ledger for the 75-member bundle) | `915b0c86b8f0e938746fbf180662e20e65377451de79a99d016c69d2625a28b1` |

**EH-3 blinded raw arm** — commit `4d8f87bd365039024745c005461192489344cb25`
(tree `3da70a615609285a7736160a22695504dbc01d2c`, 2026-08-09, "Phase A EH-3
blinded raw result bundle (immutable, pre-disclosure)").
Path `veraxis/judge-experiment/phase-a-eh3/`. Directory unchanged to HEAD.

| Member | SHA-256 |
|---|---|
| `00-EH3-BLINDED-RAW-RESULT.json` | `f0306f79fb25d9e0f2f2d93a3df4e857454a9d5ce9206006c87dc0e9f5d6f733` |
| `eh3-raw-bundle.tar.gz` (raw per-case outputs, 70 cases) | `185e2dcf24f13b94671cb1c7516e12ec585c88fae3942ae378de231ecae815f5` |
| `per-case-raw.json` | `ed1dfb55434dd2e240cd47df58d61829852862a696571b85dc5d358839e34578` |
| `run-summary.json` (per-case exit / markings / clwr / prov_exit counters) | `ea1bcfd3c2d05ba61da035562578d77a43f2e5972312d90684274ded48cd0659` |
| `bundle-manifest.json` | `e830b12ec3ebe6dc4217d3c3a2a440a87d5fcd851095357f880ba6bbc43129a6` |

## B-2. Scored commit `40712058…` — FOUND, scored-result source

Commit `40712058530a407da0710b21b0f62272809c9fe4` exists in reviewed history
(tree `1483097b0a1225be62486a4ccb278a49978497aa`, 2026-08-09, "Phase A EH-3
scored bundle (post-disclosure) + full Phase A verdict"). It is the
**scored-result source** — a distinct object from EFP commit `673a8854…`,
which it references as input (`efp_commit` field), alongside
`protocol_commit 61a470b4…` and `raw_bundle_commit 4d8f87bd…`;
`SEALED_MANIFEST_COMMITMENT_REPRODUCTION = PASS` (sealed manifest 51630 B,
sha256 `32b85214…`). Path `veraxis/judge-experiment/phase-a-eh3-scored/`,
directory unchanged to HEAD.

| Member | SHA-256 |
|---|---|
| `00-EH3-SCORED-RESULT.json` | `bda0ecb0a122e1ca96679f57f8df0c73de26bd9824a1874f8ac91919efdee164` |
| `bundle-manifest.json` | `2dba3a37fdc07b088ab1440cdba5dcfd8df03813d650a528260194ac35d706f4` |
| `case-class-binding.json` | `af77add42a0c848b1e09cda8dfdfae06df42f0247c5d929ef7481383c2b58c12` |

## B-3. Adjudication commit — FOUND, byte-bound

Commit `9f5a9adf2bc2ca65af6a55a2e1773c828e51f3a3` (tree
`31eac9bba7a3d9280d147df204dd908ffde3995d`, 2026-08-09, "Persist Phase A
v0.1 owner adjudication 001 (new record, no amendment)"). Single file
`veraxis/judge-experiment/adjudication/PHASE-A-v0.1-OWNER-ADJUDICATION-001.md`,
SHA-256 `407f5133b9595d56bebc63246fb9b0111924783dcb241cadb36360095b086f14`.

## B-4. Exact result-member hashes

Provided per bundle in B-1 / B-2 above; the in-bundle `bundle-manifest.json`
files (themselves hash-bound above) carry the per-member ledgers recorded at
freeze time, including the 75-member unmutated bundle.

## B-5. Historical execution/environment record

- **Adapter replication run**: RECORDED —
  `veraxis/judge-experiment/adapter-replication-raw/runtime-identity.json`
  (SHA-256 `42643d70ec423ac5eac5224e7a0638b2d6d65d8604b5284408de6c38871f9b51`;
  CPython 3.12.3, GCC 13.3.0 build, `/home/vitaly/venvs/torch/bin/python3`,
  `Linux-7.0.0-28-generic-x86_64-with-glibc2.39`, adapter harness sha256
  `01b07d28…`), commit `a651934225131201aebeff2d99927e1cbf6f83c4`.
- **Phase-A unmutated and EH-3 runs**: `NOT_RECORDED` — those bundles carry
  per-case exit codes and counters but no dedicated runtime/environment
  member. No reconstruction attempted.

## B-6. Currentness construction package — FOUND, byte-bound

Commit `937fe51ee75705c7b50c54bff85c87fffaa5acc2` ("Currentness construction
return: all 5 BLOCKED_CASE_CONSTRUCTION"), path
`veraxis/judge-experiment/currentness-construction/`, unchanged to HEAD.

| Member | SHA-256 |
|---|---|
| `00-CONSTRUCTION-BLOCKED-RETURN.md` | `222f0d3a5998dc77899b0b3d61d8e7ac874d4ecc3882f97f1971aaad1f25709c` |
| `blocked-cases.json` | `3129be52ae7aa127219ad60993c8270b5fed88561591bc79ef66783f0b7268c3` |
| `bundle-manifest.json` | `1a2f71f2fe92e1c52252a18a3ce51a8b8e27c508e7c89696f556b96f4963f654` |
| `search-evidence.txt` | `c644d32a1a4a66792b2b1524777e94cb3725dfff179bdb13072ecc557c8afe35` |

Governing preregistration v0.2: commit
`61772f78b98f009f93c01a21ded7a64c3d35ff19`, file
`CURRENTNESS-ROLLBACK-PREREGISTRATION-v0.2.md` 12585 B, sha256 `5c8c4bb3…`
(as stated inside the construction return itself).

## D. CDC-CLAIM-05 figure "371 Lean theorems / 21 modules / empty axiom lists" — CONFIRMED bound to the exact cited snapshot

The figure is byte-present in the frozen snapshot, not inferred from a later
state: `ZTL-theorems.txt` ("371 theorems across 21 modules, all on the empty
axiom list") is **byte-identical** (SHA-256
`fa0b34378a967c409f3c2afb2414c8b5a4b087200f923521dc035933ae1e303a`) at BOTH
pins:

- tag `veraxis-ztl-input-v0.1` → commit `e819dec7e89d2dc67d6371e1eedb8e7aae854602`;
- tag `veraxis-ztl-input-v0.2-signed` → commit `56e1ff0510c62b04dbd85bbe08b7a6deacbf276b`
  (the accepted profile pin);

and is stated in `veraxis/VERAXIS-ZTL-DOSSIER-v0.1.md` (evidence taxonomy
over the 371: 285 GENERAL / 45 BOUNDED_MODEL / 2 EXISTENCE_WITNESS /
39 CONCRETE_CELL).

**Required citation discipline (recorded, no frozen-claim change):** the
current ZTL corpus is LARGER than the pinned snapshot — the published v1.3
preprint and the CI axiom audit state 394 theorems across 25 modules
(2026-07-21 additions: identity/free-logic/ε and signature modules). So
`371 / 21` must always be cited as the **frozen snapshot figure at the
veraxis input pin**, never as the current state of ZTL; conversely, current
state must not be silently substituted into the frozen evidence binding.
This is an evidence-binding annotation for F, not an amendment of any frozen
claim.

---

Disposition of this supplement: all six traceability items resolved with
existing artifacts (`FOUND` × 5 categories; one sub-item `NOT_RECORDED` —
Phase-A/EH-3 runtime environment). Nothing `NOT_RECOVERABLE_IN_REVIEWED_HISTORY`.
Remaining Codex involvement per owner rule: delta challenge closure only.
