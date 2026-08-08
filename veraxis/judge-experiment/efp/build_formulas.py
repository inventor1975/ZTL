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
}

import hashlib, subprocess, zipfile, os
LEDGER = os.environ.get("EFP_LEDGER", "/tmp/claude-1000/-media-vitaly-SSD-1000GB-Projects-VR/62db2e38-f28f-4db8-b9a9-4ccebd1a6cc2/scratchpad/ledger")
ZIPPATH = os.path.expanduser(os.environ.get("EFP_ZIP", "~/Downloads/m1-s1-measurement-001.zip"))
CIDX = json.load(open("corpus-index.json"))
TREES = {e["head"]: e["tree"] for e in CIDX["included"] if "head" in e}
_zipf = zipfile.ZipFile(ZIPPATH)
H8c = "88a81aba060806157c6d3b63f36c0dcd1a99827a"
H10c = "3308a02ca288c2b95cbf1d56cc53c59a0140390f"

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
for n, (head, base) in EARLY.items():
    gate(f"G-{n:02d}-TREE", f"LEDGER-PR-{n:02d}",
         [REG(f"LEDGER-PR-{n:02d}", "accepted head/tree coordinate of the reviewed transaction")],
         "t_tree", [A("t_tree", "tree_identity", head=head, expected_tree=TREES[head])],
         note="Early infrastructure PRs carry thin mechanical gate content; their substance is institutional prose (expected discrepancy class: institutional).")

# ------------------------------------------------------------------- PR 5
H5, B5 = "ecdabc7ba4ca026391f0b64b6d793df67abecc29", "ec66062ed9a63fae77eeb840b766b84162059c69"
gate("G-05-TREE", "LEDGER-PR-05",
     [REG("LEDGER-PR-05", "accepted head/tree coordinate of the reviewed activation transaction")],
     "s_tree", [A("s_tree", "tree_identity", head=H5, expected_tree=TREES[H5])],
     note="The three-file-scope requirement existed only in the relay-channel order; not bindable per corpus exclusions, so the scope atom is removed and the transaction is anchored by its accepted coordinate.")

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
      A("o_tree", "tree_identity", head=H6, expected_tree=TREES[H6])])

# ------------------------------------------------------------------- PR 7
H7, B7 = "f44d1cc337d20cb8b01f85d232795b7bff93954a", "86adb7d84d4a6bb469705afc04397a8260553f23"
gate("G-07-SCOPE", "LEDGER-PR-07",
     [PA(H7, "owner-decisions/AUTHORIZE-M1-S2-LEDGER-NATIVE-EXECUTION-001.md",
         "§8: 'Authorized evidence branch: evidence/m1-s2-001 ... Authorized path class: stage-m1-s2/**'")],
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
gate("G-07-BLOCKED-SHAPE", "LEDGER-PR-07",
     [PA("88a81aba060806157c6d3b63f36c0dcd1a99827a", "owner-decisions/AUTHORIZE-M1-S2-DIAGNOSTIC-001.md",
         "§2 Frozen crash facts: began 2026-08-08T16:39:19Z; terminated SIGSEGV; exit code 139; JUnit not created; reruns 0")],
     "b_exit & b_term & b_nojunit & b_out0 & b_err0 & b_reruns & b_started",
     [A("b_exit", "json_field", head=H7, path="stage-m1-s2/05-M1-S2-AUTHORIZED-NINE-EVIDENCE.json",
        field="exit_code", expected=139),
      A("b_term", "json_field", head=H7, path="stage-m1-s2/05-M1-S2-AUTHORIZED-NINE-EVIDENCE.json",
        field="termination", expected="SIGSEGV"),
      A("b_nojunit", "file_absent", head=H7, path="stage-m1-s2/evidence/authorized-nine.junit.xml"),
      A("b_out0", "file_bytes", head=H7, path="stage-m1-s2/evidence/authorized-nine.stdout.txt", n=0),
      A("b_err0", "file_bytes", head=H7, path="stage-m1-s2/evidence/authorized-nine.stderr.txt", n=0),
      A("b_reruns", "json_field", head=H7, path="stage-m1-s2/05-M1-S2-AUTHORIZED-NINE-EVIDENCE.json",
        field="reruns", expected=0),
      A("b_started", "file_equals", head=H7, path="stage-m1-s2/evidence/authorized-nine.started-at.txt",
        literal="2026-08-08T16:39:19Z\n", alt_literal="2026-08-08T16:39:19Z")])
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
     [PA(H9, "owner-decisions/AUTHORIZE-M1-S2-DIAGNOSTIC-001.md", "§4.6: 'execute at most one normal import readline probe'; §2: SIGSEGV / exit 139 crash facts")],
     "p1_argv & p1_delta & p1_exit & p1_out & p1_err",
     [A("p1_argv", "argv_equals", head=H9, path=P9+"evidence/probes/probe-01.argv.json", argv=STANDALONE),
      A("p1_delta", "file_equals", head=H9, path=P9+"evidence/probes/probe-01.environment-delta.json",
        json_equals={}),
      A("p1_exit", "file_equals", head=H9, path=P9+"evidence/probes/probe-01.exit-code.txt",
        literal="139\n", alt_literal="139"),
      A("p1_out", "file_bytes", head=H9, path=P9+"evidence/probes/probe-01.stdout.txt", n=0),
      A("p1_err", "file_bytes", head=H9, path=P9+"evidence/probes/probe-01.stderr.txt", n=0)])
gate("G-09-PROBE2", "LEDGER-PR-09",
     [PA(H10c, "owner-decisions/AUTHORIZE-M1-CLOSURE-ENV-001-CONDITIONAL-R1-001.md", "§1 accepted diagnostic finding: 'changing only LANG, LC_ALL, and LC_CTYPE jointly from C.UTF-8 to C produced READLINE_IMPORT_OK'"),
      PA(H9, "owner-decisions/AUTHORIZE-M1-S2-DIAGNOSTIC-001.md", "§4.6: 'at most two environment-isolation variants of that same standalone probe'")],
     "p2_delta & p2_exit & p2_out & p2_err & p2_nocrash",
     [A("p2_delta", "file_equals", head=H9, path=P9+"evidence/probes/probe-02.environment-delta.json",
        json_equals={"set": {"LANG": "C", "LC_ALL": "C", "LC_CTYPE": "C"}, "unset": [],
                     "other_inherited_variables": "UNCHANGED"}),
      A("p2_exit", "file_equals", head=H9, path=P9+"evidence/probes/probe-02.exit-code.txt",
        literal="0\n", alt_literal="0"),
      A("p2_out", "file_equals", head=H9, path=P9+"evidence/probes/probe-02.stdout.txt",
        literal="READLINE_IMPORT_OK\n"),
      A("p2_err", "file_bytes", head=H9, path=P9+"evidence/probes/probe-02.stderr.txt", n=0),
      A("p2_nocrash", "file_bytes", head=H9, path=P9+"evidence/crash-diagnostics/probe-02-new-crash-reports.txt", n_max=1)])
gate("G-09-LADDER-AND-COUNTERS", "LEDGER-PR-09",
     [PA(H10c, "owner-decisions/AUTHORIZE-M1-CLOSURE-ENV-001-CONDITIONAL-R1-001.md", "§1: 'diagnostic disposition: ROOT_CAUSE_NARROWED; ROOT_CAUSE_IDENTIFIED = false; Probe 3 was not run'"),
      PA(H9, "owner-decisions/AUTHORIZE-M1-S2-DIAGNOSTIC-001.md", "§5/§7: no pytest; return dispositions; no rerun")],
     "l_disp & l_pytest & l_reruns & l_rc",
     [A("l_disp", "json_field", head=H9, path=P9+"09-M1-S2-DIAG-ADJUDICATION.json",
        field="diagnostic_disposition", expected="ROOT_CAUSE_NARROWED"),
      A("l_pytest", "json_field", head=H9, path=P9+"03-M1-S2-DIAG-PLAN-AND-COMMAND-MATRIX.json",
        field="pytest_runs", expected=0),
      A("l_reruns", "json_field", head=H9, path=P9+"03-M1-S2-DIAG-PLAN-AND-COMMAND-MATRIX.json",
        field="m1_s2_measurement_reruns", expected=0),
      A("l_rc", "json_field", head=H9, path=P9+"09-M1-S2-DIAG-ADJUDICATION.json",
        field="root_cause_claimed", expected=False)])
gate("G-09-BOUNDARY", "LEDGER-PR-09",
     [PA(H10c, "owner-decisions/AUTHORIZE-M1-CLOSURE-ENV-001-CONDITIONAL-R1-001.md", "§1: 'normal standalone import readline reproduced the frozen M1-S2 SIGSEGV'")],
     "y_same",
     [A("y_same", "file_equals", head=H9,
        path=P9+"evidence/crash-diagnostics/probe-01-stack-boundary.txt",
        equals_path=P9+"evidence/crash-diagnostics/frozen-m1-s2-stack-boundary.txt")])

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
     "z_paths & z_tree",
     [A("z_paths", "path_confinement", base=B11, head=H11, prefixes=[C]),
      A("z_tree", "tree_identity", head=H11, expected_tree=TREES[H11])])
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
     [PA(H11, "stage-m1-closure/14-M1-CLOSURE-RETURN-FINAL.md", "recorded result: 'authorized-nine 8P/1F'"),
      PA(H11, "owner-decisions/AUTHORIZE-M1-CLOSURE-ENV-001-CONDITIONAL-R1-001.md", "§B6 frozen nine-ID population; §B7 measurement sequence"),
      REG("LEDGER-PR-11", "counts verified by accepted review 4889786951")],
     "n9_counts & n9_fail",
     [A("n9_counts", "junit_counts", head=H11, path=C+"evidence/r1/authorized-nine.junit.xml",
        collected=9, passed=8, failed=1, skipped=0),
      A("n9_fail", "junit_failing_set", head=H11, path=C+"evidence/r1/authorized-nine.junit.xml",
        expected=["tests.test_audit_lineage::test_governed_success_tokens_are_distinct"])])
gate("G-11-R1-MODULE", "LEDGER-PR-11",
     [PA(H11, "stage-m1-closure/14-M1-CLOSURE-RETURN-FINAL.md", "recorded result: 'module 84P/3F'"),
      REG("LEDGER-PR-11", "counts and failing set verified by accepted review 4889786951")],
     "md_counts & md_fail",
     [A("md_counts", "junit_counts", head=H11, path=C+"evidence/r1/module.junit.xml",
        collected=87, passed=84, failed=3, skipped=0),
      A("md_fail", "junit_failing_set", head=H11, path=C+"evidence/r1/module.junit.xml",
        expected=["tests.test_audit_lineage::test_audit_003_removed_while_current_fails",
                  "tests.test_audit_lineage::test_governed_success_tokens_are_distinct",
                  "tests.test_audit_lineage::test_report_generation_requires_an_explicit_report_id"])])
gate("G-11-R1-SUITE", "LEDGER-PR-11",
     [PA(H11, "stage-m1-closure/14-M1-CLOSURE-RETURN-FINAL.md", "recorded result: 'suite 1008P/26F/7S'"),
      REG("LEDGER-PR-11", "counts verified by accepted review 4889786951")],
     "st_counts",
     [A("st_counts", "junit_counts", head=H11, path=C+"evidence/r1/suite.junit.xml",
        collected=1041, passed=1008, failed=26, skipped=7)])
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
     [PA(H11, "owner-decisions/AUTHORIZE-M1-CLOSURE-ENV-001-CONDITIONAL-R1-001.md", "§B7-B8: R1 dispositions incl. H1_FALSIFIED_BY_PREREGISTERED_R1; 'a falsified result is evidence'; §B1: original M1-S2 remains permanently BLOCKED")],
     "j_disp & j_rr & j_ce & j_blocked",
     [A("j_disp", "json_field", head=H11, path=C+"12-M1-CLOSURE-R1-ADJUDICATION.json",
        field="m1_s2_r1_disposition", expected="H1_FALSIFIED_BY_PREREGISTERED_R1"),
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
      A("zs1", "zip_member_identity", zip_sha256=ZID, member="evidence/S1-test_audit_lineage.py",
        bytes=40975, sha256="8e6f51a1613456f4a52ce37f1da8f999694fb3195da10c7dc78697b1f9c57410")])
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
        expected_changed=5, expected_hunks=7, byte_identical_unit="_isolated")])
gate("G-M1S1-NINE", "LEGACY-M1-S1-PACKAGE",
     [ZA("01-OWNER-ACCEPTANCE-CHECKPOINT-B-AND-M1-S1-EXECUTION-ORDER-001.md", "§8: execute the accepted nine-ID set; measure collected/passed/failed/skipped and exact failing IDs")],
     "z9_counts & z9_fail",
     [A("z9_counts", "junit_counts", zip_sha256=ZID, member="evidence/authorized-nine.junit.xml",
        collected=9, passed=7, failed=2, skipped=0),
      A("z9_fail", "junit_failing_set", zip_sha256=ZID, member="evidence/authorized-nine.junit.xml",
        expected=["tests.test_audit_lineage::test_governed_success_tokens_are_distinct",
                  "tests.test_audit_lineage::test_valid_confined_alternate_index_is_accepted"])])
gate("G-M1S1-MODULE", "LEGACY-M1-S1-PACKAGE",
     [ZA("01-OWNER-ACCEPTANCE-CHECKPOINT-B-AND-M1-S1-EXECUTION-ORDER-001.md", "§9: execute complete module; S0 module failures = 9 IDs; compare S1 directly to S0")],
     "zm_counts",
     [A("zm_counts", "junit_counts", zip_sha256=ZID, member="evidence/module.junit.xml",
        collected=87, passed=85, failed=2, skipped=0)])
gate("G-M1S1-SUITE", "LEGACY-M1-S1-PACKAGE",
     [ZA("01-OWNER-ACCEPTANCE-CHECKPOINT-B-AND-M1-S1-EXECUTION-ORDER-001.md", "§10: execute complete suite; S0 = 32 failing IDs / 30 functions / 9 modules; produce all six directed differences")],
     "zt_counts",
     [A("zt_counts", "junit_counts", zip_sha256=ZID, member="evidence/suite.junit.xml",
        collected=1041, passed=1009, failed=25, skipped=7)])

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
n_atoms = sum(len(g["atoms"]) for g in F)
print(f"formulas.json: {len(F)} gates, {n_atoms} atoms")
for g in F: print(" ", g["gate_id"])
