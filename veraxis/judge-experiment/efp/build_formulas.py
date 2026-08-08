#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""EFP builder: harvesting-rules.json + formulas.json for the M1 corpus.

Every formula cites its source anchor (governing document + clause) and binds
every atom to a harvesting rule with witness semantics per frozen Protocol
v0.1 (R-02/R-03: T/F only with a witness supporting that specific atom).
Constants are the accepted identities of the persisted record.
"""
import json

# ---------------------------------------------------------------- rule classes
RULES = {
 "tree_identity":     "atom is T iff `git rev-parse <head>^{tree}` equals the recorded tree; witness = the commit object itself (head sha).",
 "path_confinement":  "atom is T iff every path in `git diff --name-only <base> <head>` matches the prefix set; witness = (base, head) tree pair.",
 "changed_file_set":  "atom is T iff the changed-path set vs base equals exactly the listed set; witness = (base, head).",
 "member_identity":   "atom is T iff the artifact at <path> in the item tree has the declared bytes/sha256/sha512; witness = the blob hash.",
 "manifest_accounting": "atom is T iff declared members + the self-excluded manifest == physical files, with 0 missing / 0 undeclared / 0 duplicates and every member's bytes+sha256+sha512 reproducing; witness = manifest blob + member blobs.",
 "json_field":        "atom is T iff JSON artifact <path> has <field> == <expected>; witness = artifact blob.",
 "json_all_true":     "atom is T iff every element of <array> in <path> has <field> == true; witness = artifact blob.",
 "file_bytes":        "atom is T iff artifact <path> has exactly <n> bytes; witness = blob.",
 "file_equals":       "atom is T iff artifact <path> content equals <literal> exactly; witness = blob.",
 "file_empty_or_absent": "atom is T iff artifact <path> is absent from the tree, or present with 0 bytes where the gate expects emptiness; witness = tree listing / blob.",
 "file_absent":       "atom is T iff <path> is absent from the item tree; witness = tree object.",
 "argv_equals":       "atom is T iff JSON artifact <path> equals the exact argv list; witness = blob.",
 "junit_counts":      "atom is T iff the JUnit at <path> parses with exactly (collected,P,F,S); witness = blob.",
 "junit_failing_set": "atom is T iff the failing-ID set of the JUnit at <path> equals exactly <set>; witness = blob.",
 "junit_set_diff":    "atom is T iff failing(<A>) - failing(<B>) == <left> and failing(<B>) - failing(<A>) == <right>; witness = both blobs.",
 "zip_member_identity": "as member_identity, over the legacy zip's members; witness = zip sha256 + member name.",
 "zip_manifest_accounting": "as manifest_accounting over the legacy zip; witness = zip sha256.",
 "ast_confinement":   "atom is T iff AST module-unit diff of the two persisted sources changes exactly the listed units and no others, with the named unit byte-identical; witness = both source blobs.",
 "doc_cites":         "atom is T iff the persisted return/record document contains the exact cited line (e.g., a CI run id with SUCCESS); witness = blob. NOTE: this binds the persisted CITATION; the external CI service itself is not a corpus artifact.",
    "commit_exists":     "T iff <head> resolves to a commit object in the corpus ledger (recited head, tree not separately stipulated); unresolvable -> Z.",
    "file_present":      "T iff <path> is present in the item tree (existence only).",
    "argv_has_substr":   "T iff some element of the JSON argv at <path> contains the substring <substr>.",
    "json_field_in":     "T iff JSON <path>.<field> is one of <allowed>.",
    "junit_population":  "T iff the set of test IDs in the JUnit at <path> equals exactly <expected> (population).",
    "junit_collected":   "T iff the JUnit at <path> collects exactly <collected> cases (total).",
    "zip_member_present":"T iff <member> exists in the legacy zip.",
    "seam_contradiction":"T iff a governing clause value and the measured evidence value disagree (seam exposed).",
    "seam_f4_support":   "T iff no previously-S1-resolved test regressed in R1 (the F4 mislabel is unsupported).",
    "seam_schema_drift": "T iff two corpus manifests bind members under different field names (byte_length vs bytes).",
}

import hashlib, subprocess, zipfile, os
LEDGER = os.environ.get("EFP_LEDGER", "/tmp/claude-1000/-media-vitaly-SSD-1000GB-Projects-VR/62db2e38-f28f-4db8-b9a9-4ccebd1a6cc2/scratchpad/ledger")
ZIPPATH = os.path.expanduser(os.environ.get("EFP_ZIP", "~/Downloads/m1-s1-measurement-001.zip"))
CIDX = json.load(open("corpus-index.json"))
TREES = {e["head"]: e["tree"] for e in CIDX["included"] if "head" in e}
_zipf = zipfile.ZipFile(ZIPPATH)
H8c = "88a81aba060806157c6d3b63f36c0dcd1a99827a"
H10c = "3308a02ca288c2b95cbf1d56cc53c59a0140390f"
H5 = "ecdabc7ba4ca026391f0b64b6d793df67abecc29"
B5 = "ec66062ed9a63fae77eeb840b766b84162059c69"
H6 = "86adb7d84d4a6bb469705afc04397a8260553f23"
B6 = "ecdabc7ba4ca026391f0b64b6d793df67abecc29"
H7 = "f44d1cc337d20cb8b01f85d232795b7bff93954a"
B7 = "86adb7d84d4a6bb469705afc04397a8260553f23"
H8 = "88a81aba060806157c6d3b63f36c0dcd1a99827a"
B8 = "f44d1cc337d20cb8b01f85d232795b7bff93954a"
H9 = "6bbdaf60dea4ddeeeb820a515fa717083211c2fc"
B9 = "88a81aba060806157c6d3b63f36c0dcd1a99827a"
H10 = "3308a02ca288c2b95cbf1d56cc53c59a0140390f"
B10 = "6bbdaf60dea4ddeeeb820a515fa717083211c2fc"
H11 = "060efa2cc295e0d7d9960f725aece264fc471935"
B11 = "3308a02ca288c2b95cbf1d56cc53c59a0140390f"
P9 = "stage-m1-s2-diag/"
C = "stage-m1-closure/"
ZID = "e9250d1938bbbd5f607add695ce2273c52d00428da26481834b2dd020348d30a"

def _blob(head, path):
    r = subprocess.run(["git", "-C", LEDGER, "show", f"{head}:{path}"], capture_output=True)
    assert r.returncode == 0, (head, path)
    return r.stdout

def PA(head, path, clause):
    """Persisted-artifact anchor: hash-bound governing blob + quoted clause."""
    d = _blob(head, path)
    return {"kind": "persisted-artifact", "head": head, "path": path,
            "sha256": hashlib.sha256(d).hexdigest(), "bytes": len(d), "clause": clause}

def ZA(member, clause):
    """Legacy-zip anchor: hash-bound governing member + quoted clause."""
    d = _zipf.read(member)
    return {"kind": "legacy-zip-member",
            "zip_sha256": "e9250d1938bbbd5f607add695ce2273c52d00428da26481834b2dd020348d30a",
            "member": member, "sha256": hashlib.sha256(d).hexdigest(),
            "bytes": len(d), "clause": clause}

def REG(item, note):
    """Accepted-decision registry anchor: the frozen corpus-index entry, which
    records the accepted independent-review decision (review_id + token) and the
    accepted coordinate. Identity values anchored here derive from accepted
    decisions, not from the observed object under test."""
    e = next(x for x in CIDX["included"] if x["item_id"] == item)
    return {"kind": "accepted-decision-registry", "item_id": item,
            "review_id": e.get("review_id"),
            "accepted_review_token": e.get("accepted_review_token"), "note": note}

F = []
def gate(gid, item, anchor, formula, atoms, note=None):
    anchors = anchor if isinstance(anchor, list) else [anchor]
    F.append({"gate_id": gid, "item_id": item, "source_anchors": anchors,
              "formula": formula, "atoms": atoms, **({"note": note} if note else {})})

def A(name, rule, **kw):
    return {"atom": name, "rule": rule, "args": kw}

# ------------------------------------------------------- early infra PRs 1..4
EARLY = {
 1: ("00074eeb98517fd4cd4e76ca31758dfdda15fc93", None),
 2: ("59e4cd5c6101766a825b9cf93df7202ef1a6e254", "00074eeb98517fd4cd4e76ca31758dfdda15fc93"),
 3: ("cb38c13bad436d860b34dd75269d4fbdd648e931", "59e4cd5c6101766a825b9cf93df7202ef1a6e254"),
 4: ("ec66062ed9a63fae77eeb840b766b84162059c69", "cb38c13bad436d860b34dd75269d4fbdd648e931"),
}
H11c = "060efa2cc295e0d7d9960f725aece264fc471935"
for n, (head, base) in EARLY.items():
    if n <= 3:
        anch = [PA(H11c, "owner-decisions/REVIEW-LEDGER-BOOTSTRAP-OWNER-ACCEPTANCE-001.md",
                   "bootstrap review-chain binding: 'Reviewed head ' + head recited; trees not recited, so the gate tests recitation resolvability, not tree equality")]
    else:
        anch = [PA("ecdabc7ba4ca026391f0b64b6d793df67abecc29", "LEDGER-INVARIANTS.md",
                   "'Bootstrap acceptance is persisted at ec66062ed9a63fae77eeb840b766b84162059c69' (head recited; tree not recited)")]
    gate(f"G-{n:02d}-HEAD", f"LEDGER-PR-{n:02d}", anch,
         "t_head", [A("t_head", "commit_exists", head=head)],
         note="Early infrastructure PRs carry thin mechanical gate content; their substance is institutional prose (expected discrepancy class: institutional).")

# ------------------------------------------------------------------- PR 5
H5, B5 = "ecdabc7ba4ca026391f0b64b6d793df67abecc29", "ec66062ed9a63fae77eeb840b766b84162059c69"
gate("G-05-TREE", "LEDGER-PR-05",
     [PA(H6, "owner-decisions/AUTHORIZE-M1-S2-LEDGER-NATIVE-EXECUTION-001.md",
         "§1: 'Required activation coordinate: ledger main: ecdabc7ba4...; tree: 25f1cdab32...'")],
     "s_tree", [A("s_tree", "tree_identity", head=H5, expected_tree=TREES[H5])],
     note="Head AND tree recited in the persisted PR-06 artifact §1; the relay-only three-file-scope atom remains removed.")

# ------------------------------------------------------------------- PR 6
H6, B6 = "86adb7d84d4a6bb469705afc04397a8260553f23", "ecdabc7ba4ca026391f0b64b6d793df67abecc29"
gate("G-06-SCOPE-AND-ID", "LEDGER-PR-06",
     [PA(H6, "owner-decisions/AUTHORIZE-M1-S2-LEDGER-NATIVE-EXECUTION-001.md",
         "§9.1: 'be committed alone under owner-decisions/** on an owner/ branch'"),
      PA("f44d1cc337d20cb8b01f85d232795b7bff93954a", "stage-m1-s2/01-M1-S2-OWNER-AUTHORIZATION-REFERENCE.json",
         "persisted resolution of this artifact's bytes/SHA-256/SHA-512 and decision token"),
      REG("LEDGER-PR-06", "accepted coordinate")],
     "o_file & o_id & o_tree",
     [A("o_file", "changed_file_set", base=B6, head=H6,
        expected=["owner-decisions/AUTHORIZE-M1-S2-LEDGER-NATIVE-EXECUTION-001.md"]),
      A("o_id", "member_identity", head=H6,
        path="owner-decisions/AUTHORIZE-M1-S2-LEDGER-NATIVE-EXECUTION-001.md",
        bytes=10506,
        sha256="971ce005d0771dadf7ad7e6827c8b9f19ce63d22f408a462cad53bc014cdd020",
        sha512="b2a35c65512cf85b476814478ce0777f804d84ddbf1703fdb2c41dba35043c56390fa385e3027a1bd33739c4f1cd766a3823598c2ad6690d9f29cfbec59f5dff"),
      A("o_tree", "commit_exists", head=H6)])

# ------------------------------------------------------------------- PR 7
H7, B7 = "f44d1cc337d20cb8b01f85d232795b7bff93954a", "86adb7d84d4a6bb469705afc04397a8260553f23"
gate("G-07-SCOPE", "LEDGER-PR-07",
     [PA(H7, "owner-decisions/AUTHORIZE-M1-S2-LEDGER-NATIVE-EXECUTION-001.md",
         "§8: 'Authorized evidence branch: evidence/m1-s2-001 ... Authorized path class: stage-m1-s2/**'"),
      PA(H8c, "owner-decisions/AUTHORIZE-M1-S2-DIAGNOSTIC-001.md",
         "§1: 'ledger commit: f44d1cc3...' + 'tree: 8c48fe4b...' — persisted recitation of this transaction's coordinate")],
     "c_paths & c_tree",
     [A("c_paths", "path_confinement", base=B7, head=H7, prefixes=["stage-m1-s2/"]),
      A("c_tree", "tree_identity", head=H7, expected_tree=TREES[H7])])
gate("G-07-MANIFEST", "LEDGER-PR-07",
     [PA(H7, "owner-decisions/AUTHORIZE-M1-S2-LEDGER-NATIVE-EXECUTION-001.md",
         "§8: '12-M1-S2-EVIDENCE-MANIFEST.json is self-excluded and every member row must bind path, bytes, sha256, and sha512.'"),
      REG("LEDGER-PR-07", "accepted manifest identity 5888/1626f2b6/732d272b per review 4889282030")],
     "m_id & m_acct",
     [A("m_id", "member_identity", head=H7, path="stage-m1-s2/12-M1-S2-EVIDENCE-MANIFEST.json",
        bytes=5888, sha256="1626f2b608fda34f56e4a8ddb3c39e229f510028322d923a061e4606e216cdf8",
        sha512="732d272b5dcb2c9c842779e3584eb3af688c997a039ced11087477cd406b760e435291a008fe93593a84e194ef854c8fe5965d1c23d4156cf0547079ec41b580"),
      A("m_acct", "manifest_accounting", head=H7,
        manifest="stage-m1-s2/12-M1-S2-EVIDENCE-MANIFEST.json", root="stage-m1-s2/",
        member_field_bytes="bytes")])
gate("G-07-AUTHREF", "LEDGER-PR-07",
     [PA(H7, "owner-decisions/AUTHORIZE-M1-S2-LEDGER-NATIVE-EXECUTION-001.md",
         "§8: '01-M1-S2-OWNER-AUTHORIZATION-REFERENCE.json must resolve this persisted owner-decision artifact by exact ledger commit, ledger path, bytes, SHA-256, SHA-512, and owner decision identifier.'")],
     "a_commit & a_bytes & a_sha & a_token & a_state",
     [A("a_commit", "json_field", head=H7, path="stage-m1-s2/01-M1-S2-OWNER-AUTHORIZATION-REFERENCE.json",
        field="ledger_commit", expected="86adb7d84d4a6bb469705afc04397a8260553f23"),
      A("a_bytes", "json_field", head=H7, path="stage-m1-s2/01-M1-S2-OWNER-AUTHORIZATION-REFERENCE.json",
        field="bytes", expected=10506),
      A("a_sha", "json_field", head=H7, path="stage-m1-s2/01-M1-S2-OWNER-AUTHORIZATION-REFERENCE.json",
        field="sha256", expected="971ce005d0771dadf7ad7e6827c8b9f19ce63d22f408a462cad53bc014cdd020"),
      A("a_token", "json_field", head=H7, path="stage-m1-s2/01-M1-S2-OWNER-AUTHORIZATION-REFERENCE.json",
        field="decision", expected="AUTHORIZE_M1_S2_LEDGER_NATIVE_EXECUTION_001"),
      A("a_state", "json_field", head=H7, path="stage-m1-s2/01-M1-S2-OWNER-AUTHORIZATION-REFERENCE.json",
        field="state", expected="ACCEPTED_STATE_PERSISTED")])
gate("G-07-EVIDENCE-COMPLETENESS", "LEDGER-PR-07",
     [PA(H7, "owner-decisions/AUTHORIZE-M1-S2-LEDGER-NATIVE-EXECUTION-001.md",
         "§8: 'The M1-S2 evidence record must include at minimum: 01-... 11-M1-S2-RETURN-FINAL.md ... all raw JUnit/stdout/stderr execution evidence; self-excluded manifest' — pre-result stipulation; the observed crash-shape values (SIGSEGV/139/absent JUnit) are ground truth, not gate conditions")],
     "ev01 & ev05 & ev10 & ev_exec & ev_out & ev_err",
     [A("ev01", "file_present", head=H7, path="stage-m1-s2/01-M1-S2-OWNER-AUTHORIZATION-REFERENCE.json"),
      A("ev05", "file_present", head=H7, path="stage-m1-s2/05-M1-S2-AUTHORIZED-NINE-EVIDENCE.json"),
      A("ev10", "file_present", head=H7, path="stage-m1-s2/11-M1-S2-RETURN-FINAL.md"),
      A("ev_exec", "file_present", head=H7, path="stage-m1-s2/evidence/authorized-nine.execution.json"),
      A("ev_out", "file_present", head=H7, path="stage-m1-s2/evidence/authorized-nine.stdout.txt"),
      A("ev_err", "file_present", head=H7, path="stage-m1-s2/evidence/authorized-nine.stderr.txt")])
gate("G-07-CRASH-ID", "LEDGER-PR-07",
     [PA("88a81aba060806157c6d3b63f36c0dcd1a99827a", "owner-decisions/AUTHORIZE-M1-S2-DIAGNOSTIC-001.md",
         "§2: crash report path/bytes/SHA-256/SHA-512 = python3.12-...ips / 16911 / 4a343442... / b51d6598...")],
     "cr_id",
     [A("cr_id", "member_identity", head=H7,
        path="stage-m1-s2/evidence/python3.12-2026-08-08-123926.ips",
        bytes=16911, sha256="4a343442366292db116a75d9e4e192acd86cdcf0492df3adef0b64e41f1a7ef4",
        sha512="b51d659885b5029658925f304fa52e05e11c19f6ad4f09c9ac5a5f5e1a86cc87d4291c512f6c672a500adb918a606e17f3c6f89847d89155bd5677f654324e0e")])

# ------------------------------------------------------------------- PR 8
H8, B8 = "88a81aba060806157c6d3b63f36c0dcd1a99827a", "f44d1cc337d20cb8b01f85d232795b7bff93954a"
gate("G-08-ID", "LEDGER-PR-08",
     [PA("6bbdaf60dea4ddeeeb820a515fa717083211c2fc", "stage-m1-s2-diag/01-M1-S2-DIAG-OWNER-AUTHORIZATION-REFERENCE.json",
         "persisted resolution of this artifact's bytes/SHA-256/SHA-512 and decision token"),
      REG("LEDGER-PR-08", "accepted coordinate; one-file-scope requirement existed only in the relay order — scope atom removed")],
     "d_id & d_tree",
     [A("d_id", "member_identity", head=H8, path="owner-decisions/AUTHORIZE-M1-S2-DIAGNOSTIC-001.md",
        bytes=7570, sha256="3fae0fe4bdf8c60761ff9d6c25e5122280b9553f906fbf8f7952130b61d3a321",
        sha512="beb373b61897ec95a8887facdd162750673a67c4a57db4db09a5b2dce40657412101bcde444afab0c683914c62c037a89e5d31da1e24aac89c80ae4286a4954b"),
      A("d_tree", "tree_identity", head=H8, expected_tree=TREES[H8])])

# ------------------------------------------------------------------- PR 9
H9, B9 = "6bbdaf60dea4ddeeeb820a515fa717083211c2fc", "88a81aba060806157c6d3b63f36c0dcd1a99827a"
P9 = "stage-m1-s2-diag/"
gate("G-09-SCOPE", "LEDGER-PR-09",
     [PA(H9, "owner-decisions/AUTHORIZE-M1-S2-DIAGNOSTIC-001.md", "§4: 'Authorized evidence branch: evidence/m1-s2-diag-001 ... Authorized ledger path: stage-m1-s2-diag/**'")],
     "g_paths & g_tree",
     [A("g_paths", "path_confinement", base=B9, head=H9, prefixes=[P9]),
      A("g_tree", "tree_identity", head=H9, expected_tree=TREES[H9])])
gate("G-09-MANIFEST", "LEDGER-PR-09",
     [PA(H9, "owner-decisions/AUTHORIZE-M1-S2-DIAGNOSTIC-001.md", "§8: 'self-excluded evidence manifest binding each member by path, bytes, sha256, sha512'"),
      REG("LEDGER-PR-09", "accepted manifest identity 69457/b210ee6c/15f659d3 per review 4889536531")],
     "n_id & n_acct",
     [A("n_id", "member_identity", head=H9, path=P9+"12-M1-S2-DIAG-EVIDENCE-MANIFEST.json",
        bytes=69457, sha256="b210ee6cccb622d43d47c62c841aad7ab683b40a4ea9c8a3d10c55f55f8651d4",
        sha512="15f659d331fb9ad1975e4faf801384d182f0eca442f14b138a731435f4663bd985b96b6d8dd89406ddbd73754e934f48542a92cfa969f0fbd36e244de9b473c3"),
      A("n_acct", "manifest_accounting", head=H9, manifest=P9+"12-M1-S2-DIAG-EVIDENCE-MANIFEST.json",
        root=P9, member_field_bytes="bytes")])
STANDALONE = ["/Users/arkadiymiteiko/oam-cdc-reference-publication-candidate/.venv/bin/python",
              "-c", "import readline; print('READLINE_IMPORT_OK')"]
gate("G-09-PROBE1", "LEDGER-PR-09",
     [PA(H9, "owner-decisions/AUTHORIZE-M1-S2-DIAGNOSTIC-001.md",
         "§4.6: 'execute at most one normal import readline probe'; §4.7: 'preserve stdout, stderr, exit status, exact argv/environment delta' — the probe's observed outcome values are ground truth, not stipulated expectations")],
     "p1_code & p1_argv & p1_delta & p1_exit & p1_out & p1_err",
     [A("p1_code", "argv_has_substr", head=H9, path=P9+"evidence/probes/probe-01.argv.json",
        substr="import readline"),
      A("p1_argv", "file_present", head=H9, path=P9+"evidence/probes/probe-01.argv.json"),
      A("p1_delta", "file_present", head=H9, path=P9+"evidence/probes/probe-01.environment-delta.json"),
      A("p1_exit", "file_present", head=H9, path=P9+"evidence/probes/probe-01.exit-code.txt"),
      A("p1_out", "file_present", head=H9, path=P9+"evidence/probes/probe-01.stdout.txt"),
      A("p1_err", "file_present", head=H9, path=P9+"evidence/probes/probe-01.stderr.txt")])
gate("G-09-PROBE2", "LEDGER-PR-09",
     [PA(H9, "owner-decisions/AUTHORIZE-M1-S2-DIAGNOSTIC-001.md",
         "§4.6: 'at most two environment-isolation variants of that same standalone probe' — same python code required; probe count bounded at three; observed outcome values are ground truth")],
     "p2_code & p2_delta & p2_exit & p2_out & p2_err & p_no4",
     [A("p2_code", "argv_has_substr", head=H9, path=P9+"evidence/probes/probe-02.argv.json",
        substr="import readline"),
      A("p2_delta", "file_present", head=H9, path=P9+"evidence/probes/probe-02.environment-delta.json"),
      A("p2_exit", "file_present", head=H9, path=P9+"evidence/probes/probe-02.exit-code.txt"),
      A("p2_out", "file_present", head=H9, path=P9+"evidence/probes/probe-02.stdout.txt"),
      A("p2_err", "file_present", head=H9, path=P9+"evidence/probes/probe-02.stderr.txt"),
      A("p_no4", "file_absent", head=H9, path=P9+"evidence/probes/probe-04.argv.json")])
gate("G-09-LADDER-AND-COUNTERS", "LEDGER-PR-09",
     [PA(H9, "owner-decisions/AUTHORIZE-M1-S2-DIAGNOSTIC-001.md",
         "§7: 'Return exactly one: ROOT_CAUSE_IDENTIFIED / ROOT_CAUSE_NARROWED / ROOT_CAUSE_UNRESOLVED / DIAGNOSTIC_BLOCKED'; §5: no pytest, no rerunning authorized-nine — the specific NARROWED value is ground truth")],
     "l_disp_vocab & l_pytest & l_reruns",
     [A("l_disp_vocab", "json_field_in", head=H9, path=P9+"09-M1-S2-DIAG-ADJUDICATION.json",
        field="diagnostic_disposition",
        allowed=["ROOT_CAUSE_IDENTIFIED", "ROOT_CAUSE_NARROWED", "ROOT_CAUSE_UNRESOLVED", "DIAGNOSTIC_BLOCKED"]),
      A("l_pytest", "json_field", head=H9, path=P9+"03-M1-S2-DIAG-PLAN-AND-COMMAND-MATRIX.json",
        field="pytest_runs", expected=0),
      A("l_reruns", "json_field", head=H9, path=P9+"03-M1-S2-DIAG-PLAN-AND-COMMAND-MATRIX.json",
        field="m1_s2_measurement_reruns", expected=0)])
gate("G-09-BOUNDARY-EVIDENCE", "LEDGER-PR-09",
     [PA(H9, "owner-decisions/AUTHORIZE-M1-S2-DIAGNOSTIC-001.md",
         "§6.F: 'Compare those observations to the frozen crash report' — requires both comparanda preserved; the equality outcome is ground truth")],
     "y_frozen & y_probe",
     [A("y_frozen", "file_present", head=H9, path=P9+"evidence/crash-diagnostics/frozen-m1-s2-stack-boundary.txt"),
      A("y_probe", "file_present", head=H9, path=P9+"evidence/crash-diagnostics/probe-01-stack-boundary.txt")])

# ------------------------------------------------------------------- PR 10
H10, B10 = "3308a02ca288c2b95cbf1d56cc53c59a0140390f", "6bbdaf60dea4ddeeeb820a515fa717083211c2fc"
gate("G-10-ID", "LEDGER-PR-10",
     [PA("060efa2cc295e0d7d9960f725aece264fc471935", "stage-m1-closure/01-M1-CLOSURE-OWNER-AUTHORIZATION-REFERENCE.json",
         "persisted resolution of this artifact's identity, ratification and persistence events"),
      REG("LEDGER-PR-10", "accepted coordinate; net-one-file requirement existed only in the relay order — scope atom removed")],
     "r_id & r_tree",
     [A("r_id", "member_identity", head=H10,
        path="owner-decisions/AUTHORIZE-M1-CLOSURE-ENV-001-CONDITIONAL-R1-001.md",
        bytes=20814, sha256="e485d95eaa0416f8ac3c1a7666b3357a21f64d454c8b188f70da5169bc083ad7",
        sha512="c4a58c6e3dd176f3c7f81ca4baed55311e89adeec72725eaa30e83e48d062b1cf944f95cc750a3de22b685565f02fecc09daf61e8dffca796fe3a0aaa6527841"),
      A("r_tree", "tree_identity", head=H10, expected_tree=TREES[H10])])

# ------------------------------------------------------------------- PR 11
H11, B11 = "060efa2cc295e0d7d9960f725aece264fc471935", "3308a02ca288c2b95cbf1d56cc53c59a0140390f"
C = "stage-m1-closure/"
gate("G-11-SCOPE", "LEDGER-PR-11",
     [PA(H11, "owner-decisions/AUTHORIZE-M1-CLOSURE-ENV-001-CONDITIONAL-R1-001.md", "§8: 'Branch: evidence/m1-closure-001 ... Paths: stage-m1-closure/**'")],
     "z_paths",
     [A("z_paths", "path_confinement", base=B11, head=H11, prefixes=[C])],
     note="PR-11 is the terminal transaction; its coordinate has no downstream persisted recitation, so the tree atom is removed — the coordinate lives in ground truth (accepted decision registry).")
gate("G-11-MANIFEST", "LEDGER-PR-11",
     [PA(H11, "owner-decisions/AUTHORIZE-M1-CLOSURE-ENV-001-CONDITIONAL-R1-001.md", "§8: 'The manifest is self-excluded and must bind every other persisted member by path, bytes, SHA-256, and SHA-512.'"),
      REG("LEDGER-PR-11", "accepted manifest identity 36845/8aca2ce0/d24422f0 per review 4889786951")],
     "w_id & w_acct",
     [A("w_id", "member_identity", head=H11, path=C+"15-M1-CLOSURE-EVIDENCE-MANIFEST.json",
        bytes=36845, sha256="8aca2ce0ba631b2cc62f41bf774329dcc459415db09d7fcadc0137ab1327a1e3",
        sha512="d24422f0cf920b6acb1c5c939e9ba1742c7173d5fd77fcfcaac249ab14f87c8f2bf46657c6394f4d47d90b52a7359c172709f3fbcd9266e95b07a0e3a9f73d43"),
      A("w_acct", "manifest_accounting", head=H11, manifest=C+"15-M1-CLOSURE-EVIDENCE-MANIFEST.json",
        root=C, member_field_bytes="bytes")])
QUAL_ARGV = ["/usr/bin/env", "LANG=C", "LC_ALL=C", "LC_CTYPE=C"] + STANDALONE
qa = []
for t in ("01", "02", "03"):
    qa += [A(f"q{t}_argv", "argv_equals", head=H11, path=C+f"evidence/phase-a/QUAL_TRIAL_{t}.argv.json", argv=QUAL_ARGV),
           A(f"q{t}_exit", "file_equals", head=H11, path=C+f"evidence/phase-a/QUAL_TRIAL_{t}.exit-code.txt",
             literal="0\n", alt_literal="0"),
           A(f"q{t}_out", "file_equals", head=H11, path=C+f"evidence/phase-a/QUAL_TRIAL_{t}.stdout.txt",
             literal="READLINE_IMPORT_OK\n"),
           A(f"q{t}_err", "file_bytes", head=H11, path=C+f"evidence/phase-a/QUAL_TRIAL_{t}.stderr.txt", n=0),
           A(f"q{t}_nc", "file_bytes", head=H11, path=C+f"evidence/phase-a/QUAL_TRIAL_{t}.new-crash-reports.txt", n_max=1)]
gate("G-11-TRIALS", "LEDGER-PR-11",
     [PA(H11, "owner-decisions/AUTHORIZE-M1-CLOSURE-ENV-001-CONDITIONAL-R1-001.md", "§5.A5 exact trial argv semantics; §6.6-10: three trials attempted once, exit 0, stdout exactly READLINE_IMPORT_OK + terminating newline, stderr zero bytes, no crash report")],
     " & ".join(a["atom"] for a in qa), qa)
gate("G-11-ACTIVATION", "LEDGER-PR-11",
     [PA(H11, "owner-decisions/AUTHORIZE-M1-CLOSURE-ENV-001-CONDITIONAL-R1-001.md", "§6: 'Phase B authority becomes ACTIVE_BY_PREAUTHORIZED_CONDITION if and only if all of the following are true and recorded' (P01-P18)")],
     "act_all & act_auth",
     [A("act_all", "json_all_true", head=H11, path=C+"05-M1-CLOSURE-PHASE-A-ACTIVATION.json",
        array="predicates", field="proven"),
      A("act_auth", "json_field", head=H11, path=C+"05-M1-CLOSURE-PHASE-A-ACTIVATION.json",
        field="phase_b_authority", expected="ACTIVE_BY_PREAUTHORIZED_CONDITION")])
gate("G-11-R1-NINE", "LEDGER-PR-11",
     [PA(H11, A10c := "owner-decisions/AUTHORIZE-M1-CLOSURE-ENV-001-CONDITIONAL-R1-001.md",
         "§B6: 'The first scientific command must target exactly these nine IDs and no others' (population stipulated pre-result); §B7: result-bearing = parseable JUnit for the intended population — the observed 8P/1F is ground truth, not a stipulated expectation")],
     "n9_pop",
     [A("n9_pop", "junit_population", head=H11, path=C+"evidence/r1/authorized-nine.junit.xml",
        expected=['tests.test_audit_lineage::test_operational_index_validates_and_verifies', 'tests.test_audit_lineage::test_supersession_lineage_is_a_single_normalized_graph', 'tests.test_audit_lineage::test_currentness_is_unaffected_by_filesystem_tricks[higher numbered unindexed report]', 'tests.test_audit_lineage::test_currentness_is_unaffected_by_filesystem_tricks[newer modification time]', 'tests.test_audit_lineage::test_currentness_is_unaffected_by_filesystem_tricks[lexically later name]', 'tests.test_audit_lineage::test_governed_success_tokens_are_distinct', 'tests.test_audit_lineage::test_focused_audit_tests_do_not_mutate_the_reviewed_repository', 'tests.test_audit_lineage::test_valid_confined_alternate_index_is_accepted', 'tests.test_audit_lineage::test_lineage_is_a_single_root_injective_linear_chain'])])
gate("G-11-R1-MODULE", "LEDGER-PR-11",
     [PA(H11, A10c,
         "§B7: 'tests/test_audit_lineage.py module' executed once, result-bearing; §B2: 'S1 module predecessor: 85P / 2F' stipulates the 87-ID module population pre-result — the observed 84P/3F is ground truth")],
     "md_coll",
     [A("md_coll", "junit_collected", head=H11, path=C+"evidence/r1/module.junit.xml", collected=87)])
gate("G-11-R1-SUITE", "LEDGER-PR-11",
     [PA(H11, A10c,
         "§B5: 'total suite collected: 1041' (stipulated pre-result); §B7: full suite once, result-bearing — the observed 1008P/26F/7S is ground truth")],
     "st_coll",
     [A("st_coll", "junit_collected", head=H11, path=C+"evidence/r1/suite.junit.xml", collected=1041)])
gate("G-11-EDIT-IDS", "LEDGER-PR-11",
     [PA(H11, "owner-decisions/AUTHORIZE-M1-CLOSURE-ENV-001-CONDITIONAL-R1-001.md", "§B3: exact post-edit identities (_isolated 9a11894f...; file 40975 / 04bd2679... / 5c56b9a1...); 'no second scientific edit is authorized'")],
     "e_cnt & e_iso & e_bytes & e_sha & e_sha512",
     [A("e_cnt", "json_field", head=H11, path=C+"06-M1-CLOSURE-R1-RECONSTRUCTION-CONFINEMENT.json",
        field="scientific_edits", expected=1),
      A("e_iso", "json_field", head=H11, path=C+"06-M1-CLOSURE-R1-RECONSTRUCTION-CONFINEMENT.json",
        field="isolated_sha256", expected="9a11894fc361911fe9a6273062686e88e9018b2299aa61a1f03373919a4c19d8"),
      A("e_bytes", "json_field", head=H11, path=C+"06-M1-CLOSURE-R1-RECONSTRUCTION-CONFINEMENT.json",
        field="post_test_bytes", expected=40975),
      A("e_sha", "json_field", head=H11, path=C+"06-M1-CLOSURE-R1-RECONSTRUCTION-CONFINEMENT.json",
        field="post_test_sha256", expected="04bd2679de95ec831ba010d99fee1cb578f70497916951035e9518340371f2cc"),
      A("e_sha512", "json_field", head=H11, path=C+"06-M1-CLOSURE-R1-RECONSTRUCTION-CONFINEMENT.json",
        field="post_test_sha512", expected="5c56b9a105122586e1fe1d26855d54d5b695179dbd1d7325a8b1f714f0c2dd397e45361a6dfa5b1b949eb9b1b347e9095477a96eb65e69aa5f0fbed3a0046f9b")])
gate("G-11-ADJUDICATION", "LEDGER-PR-11",
     [PA(H11, A10c,
         "§B7-B8: disposition vocabulary {H1_SUPPORTED_BY_PREREGISTERED_R1, H1_FALSIFIED_BY_PREREGISTERED_R1, BLOCKED_INFRASTRUCTURE}; §9: no R1 rerun, no retry-until-green; §B1: 'The original M1-S2 remains permanently BLOCKED' — all pre-result; the specific FALSIFIED value is ground truth")],
     "j_vocab & j_rr & j_ce & j_blocked",
     [A("j_vocab", "json_field_in", head=H11, path=C+"12-M1-CLOSURE-R1-ADJUDICATION.json",
        field="m1_s2_r1_disposition",
        allowed=["H1_SUPPORTED_BY_PREREGISTERED_R1", "H1_FALSIFIED_BY_PREREGISTERED_R1",
                 "BLOCKED_INFRASTRUCTURE", "NOT_EXECUTED_PHASE_B_INACTIVE"]),
      A("j_rr", "json_field", head=H11, path=C+"12-M1-CLOSURE-R1-ADJUDICATION.json",
        field="r1_reruns", expected=0),
      A("j_ce", "json_field", head=H11, path=C+"12-M1-CLOSURE-R1-ADJUDICATION.json",
        field="corrective_edits", expected=0),
      A("j_blocked", "json_field", head=H11, path=C+"12-M1-CLOSURE-R1-ADJUDICATION.json",
        field="original_m1_s2", expected="BLOCKED")])

# --------------------------------------------------------------- LEGACY M1-S1
ZID = "e9250d1938bbbd5f607add695ce2273c52d00428da26481834b2dd020348d30a"
gate("G-M1S1-ACCOUNTING", "LEGACY-M1-S1-PACKAGE",
     [ZA("01-OWNER-ACCEPTANCE-CHECKPOINT-B-AND-M1-S1-EXECUTION-ORDER-001.md", "§13: package accounting — manifest derived from actual members; missing 0 / undeclared 0 / duplicates 0 / identity mismatches 0; self-excluded manifest")],
     "za_acct",
     [A("za_acct", "zip_manifest_accounting", zip_sha256=ZID,
        manifest="11-M1-S1-PACKAGE-MANIFEST.json", member_field_bytes="byte_length")],
     note="This package uses `byte_length` where ledger manifests use `bytes` — the persisted schema-drift seam S-5.")
gate("G-M1S1-FILE-IDS", "LEGACY-M1-S1-PACKAGE",
     [ZA("01-OWNER-ACCEPTANCE-CHECKPOINT-B-AND-M1-S1-EXECUTION-ORDER-001.md", "§3: S0 test-file bytes 40741, SHA-256 582906...; §6: S1 test-file bytes/SHA-256/SHA-512 required")],
     "zs0 & zs1",
     [A("zs0", "zip_member_identity", zip_sha256=ZID, member="evidence/S0-test_audit_lineage.py",
        bytes=40741, sha256="582906143f3c740e9889562d7719eb09d236a9107eb8c3df64e1fd46de8e9476"),
      A("zs1", "zip_member_present", zip_sha256=ZID, member="evidence/S1-test_audit_lineage.py")],
     note="§6 stipulates that S1 identities be computed and recorded; the specific S1 values are results — ground truth, not gate conditions. The gate requires presence of both sources; S0's identity IS pre-stipulated (§3) and stays exact.")
gate("G-M1S1-CONFINEMENT", "LEGACY-M1-S1-PACKAGE",
     [ZA("01-OWNER-ACCEPTANCE-CHECKPOINT-B-AND-M1-S1-EXECUTION-ORDER-001.md", "§4: only the seven enumerated functions may receive semantic edits; _isolated must remain byte-for-byte at S0; §5: seven enumerated sites; EXECUTION NOTE: seven sites fall inside five functions")],
     "zc_ast",
     [A("zc_ast", "ast_confinement", zip_sha256=ZID,
        s0="evidence/S0-test_audit_lineage.py", s1="evidence/S1-test_audit_lineage.py",
        allowed_units=["test_operational_index_validates_and_verifies",
                       "test_supersession_lineage_is_a_single_normalized_graph",
                       "test_currentness_is_unaffected_by_filesystem_tricks",
                       "test_governed_success_tokens_are_distinct",
                       "test_focused_audit_tests_do_not_mutate_the_reviewed_repository",
                       "test_valid_confined_alternate_index_is_accepted",
                       "test_lineage_is_a_single_root_injective_linear_chain"],
        expected_hunks=7, byte_identical_unit="_isolated")],
     note="§5 pre-stipulates seven sites and §4 the frozen fixture; the measured five-function count is a result (and the substance of seam S-1) — ground truth, not a gate condition.")
gate("G-M1S1-NINE", "LEGACY-M1-S1-PACKAGE",
     [ZA("01-OWNER-ACCEPTANCE-CHECKPOINT-B-AND-M1-S1-EXECUTION-ORDER-001.md", "§8: execute the accepted nine-ID set; measure collected/passed/failed/skipped and exact failing IDs")],
     "z9_coll",
     [A("z9_coll", "junit_collected", zip_sha256=ZID, member="evidence/authorized-nine.junit.xml",
        collected=9)],
     note="§8: 'Do not assume the expected result. Measure.' — the 7P/2F outcome is ground truth; the stipulated content is the nine-ID execution with a parseable result.")
gate("G-M1S1-MODULE", "LEGACY-M1-S1-PACKAGE",
     [ZA("01-OWNER-ACCEPTANCE-CHECKPOINT-B-AND-M1-S1-EXECUTION-ORDER-001.md", "§9: execute complete module; S0 module failures = 9 IDs; compare S1 directly to S0")],
     "zm_coll",
     [A("zm_coll", "junit_collected", zip_sha256=ZID, member="evidence/module.junit.xml",
        collected=87)],
     note="87 collected is stipulated by the accepted S0 state recited in §1 ('module = 87 collected'); 85P/2F is ground truth.")
gate("G-M1S1-SUITE", "LEGACY-M1-S1-PACKAGE",
     [ZA("01-OWNER-ACCEPTANCE-CHECKPOINT-B-AND-M1-S1-EXECUTION-ORDER-001.md", "§10: execute complete suite; S0 = 32 failing IDs / 30 functions / 9 modules; produce all six directed differences")],
     "zt_coll",
     [A("zt_coll", "junit_collected", zip_sha256=ZID, member="evidence/suite.junit.xml",
        collected=1041)],
     note="1041 total is stipulated by the accepted S0 state recited in §1 ('suite = 1041 total'); 1009P/25F/7S is ground truth.")

# ---------------------------------------------------- operational seam gates
ORDERM = "01-OWNER-ACCEPTANCE-CHECKPOINT-B-AND-M1-S1-EXECUTION-ORDER-001.md"
gate("SEAM-S1-METRIC-CONTRADICTION", "LEGACY-M1-S1-PACKAGE",
     [ZA(ORDERM, "govering: 'authorized functions changed = 7'"),
      ZA("03-M1-S1-CHANGE-CONFINEMENT-REPORT.json", "measured: authorized_functions_changed = 5")],
     "~s1_seam",
     [A("s1_seam", "seam_contradiction", zip_sha256=ZID,
        governing_member=ORDERM, governing_regex=r"authorized functions changed\s*=\s*(\d+)",
        measured_member="03-M1-S1-CHANGE-CONFINEMENT-REPORT.json",
        measured_field="authorized_functions_changed")],
     note="S-1 detection: T iff governing 7 and measured 5 disagree. The historical defect is preserved as the condition tested; MISSED = values agreed / normalized away.")
gate("SEAM-S4-F4-MISLABEL", "LEDGER-PR-11",
     [PA("060efa2cc295e0d7d9960f725aece264fc471935", C+"12-M1-CLOSURE-R1-ADJUDICATION.json",
         "triggered_conditions include F4"),
      REG("LEDGER-PR-11", "owner ruled F4 NOT_SUSTAINED_AS_LABELED")],
     "~s4_seam",
     [A("s4_seam", "seam_f4_support", head="060efa2cc295e0d7d9960f725aece264fc471935",
        suite=C+"evidence/r1/suite.junit.xml",
        seven_resolved=["tests.test_audit_lineage::test_operational_index_validates_and_verifies",
                        "tests.test_audit_lineage::test_supersession_lineage_is_a_single_normalized_graph",
                        "tests.test_audit_lineage::test_currentness_is_unaffected_by_filesystem_tricks[higher numbered unindexed report]",
                        "tests.test_audit_lineage::test_currentness_is_unaffected_by_filesystem_tricks[newer modification time]",
                        "tests.test_audit_lineage::test_currentness_is_unaffected_by_filesystem_tricks[lexically later name]",
                        "tests.test_audit_lineage::test_focused_audit_tests_do_not_mutate_the_reviewed_repository",
                        "tests.test_audit_lineage::test_lineage_is_a_single_root_injective_linear_chain"])],
     note="S-4 detection: T iff none of the seven S1-resolved tests regressed in R1 (F4 per B8-4 unsupported). MISSED = a regression found, endorsing F4.")
gate("SEAM-S5-SCHEMA-DRIFT", "LEGACY-M1-S1-PACKAGE",
     [ZA("11-M1-S1-PACKAGE-MANIFEST.json", "binds members by 'byte_length'"),
      PA("f44d1cc337d20cb8b01f85d232795b7bff93954a", "stage-m1-s2/12-M1-S2-EVIDENCE-MANIFEST.json",
         "binds members by 'bytes'")],
     "~s5_seam",
     [A("s5_seam", "seam_schema_drift", zip_sha256=ZID,
        zip_manifest="11-M1-S1-PACKAGE-MANIFEST.json",
        ledger_head="f44d1cc337d20cb8b01f85d232795b7bff93954a",
        ledger_manifest="stage-m1-s2/12-M1-S2-EVIDENCE-MANIFEST.json")],
     note="S-5 detection: T iff the two manifests bind members under different field names. MISSED = drift silently absorbed.")

out = {"formula_set_id": "M1-EXPERIMENT-FORMULAS-v0.1",
       "protocol_commit": "61a470b41eccf8e57633d0abee7bbc795329a411",
       "judge_dialect": "ztljudge string formulas over named atoms; conjunction '&'",
       "rules": RULES, "gates": F}
json.dump(out, open("formulas.json", "w"), indent=1, ensure_ascii=False)
json.dump({"harvesting_rules_id": "M1-EXPERIMENT-HARVESTING-RULES-v0.1",
           "provenance": "Every T/F atom carries witness = (corpus item identity, artifact path, blob/zip hash, rule id). Whatever a rule cannot support enters as Z. No manual patching. Witness must support the SPECIFIC atom at the SPECIFIC status (Protocol R-02/R-03).",
           "default": "Z (default-deny)",
           "rules": RULES},
          open("harvesting-rules.json", "w"), indent=1, ensure_ascii=False)
# ---- regenerate ClaimContext templates from the FINAL gate set (revision 4)
_tpl = {"templates_id": "M1-EXPERIMENT-CLAIM-CONTEXT-TEMPLATES-v0.1",
        "model": "ClaimContext = stipulation identity + authority identity + institutional reading/scope + JudgeContext identity (frozen Protocol §2). The institutional portion below is frozen per gate; JudgeContext identity is computed at evaluation time; ClaimContext identity is the SHA-256 of the canonical JSON of the combined tuple.",
        "canonicalization": "json.dumps(obj, sort_keys=True, separators=(',',':')), UTF-8",
        "gates": {}}
for g in F:
    a0 = g["source_anchors"][0]
    gid = g["gate_id"]
    if gid.startswith("SEAM-"):
        stip = {"kind": "experiment-freeze-package", "protocol_commit": "61a470b41eccf8e57633d0abee7bbc795329a411",
                "seam_gate": gid}
        auth = "Experiment authority under frozen Protocol v0.1 §22/§28 and the Experiment Freeze Package (steering: V. Reznik). NOT stipulated by the historical institution."
        scope = f"Known-seam evaluation claim: EH-2 detection of the seam bound in seam-detection-mapping.json for {gid}."
    else:
        if a0["kind"] == "persisted-artifact":
            stip = {"kind": a0["kind"], "head": a0["head"], "path": a0["path"], "sha256": a0["sha256"]}
            auth = ("Arkadiy Miteiko, Owner / Design Authority (persisted owner-decision artifact)"
                    if a0["path"].startswith("owner-decisions/")
                    else "Implementer evidence record under owner authorization; accepted by independent review")
        elif a0["kind"] == "legacy-zip-member":
            stip = {"kind": a0["kind"], "zip_sha256": a0["zip_sha256"], "member": a0["member"], "sha256": a0["sha256"]}
            auth = "Arkadiy Miteiko, Owner / Design Authority (verbatim owner order persisted in the accepted package)"
        else:
            stip = {"kind": a0["kind"], "item_id": a0["item_id"], "review_id": a0.get("review_id")}
            auth = "Accepted independent-review decision (inventor1975) + owner acceptance of record"
        scope = f"{g['item_id']}: {a0.get('clause', a0.get('note',''))}"
    _tpl["gates"][gid] = {"stipulation_identity": stip, "authority_identity": auth,
                          "institutional_reading_scope": scope}
json.dump(_tpl, open("claim-context-templates.json", "w"), indent=1, ensure_ascii=False)

n_atoms = sum(len(g["atoms"]) for g in F)
print(f"formulas.json: {len(F)} gates, {n_atoms} atoms")
for g in F: print(" ", g["gate_id"])
