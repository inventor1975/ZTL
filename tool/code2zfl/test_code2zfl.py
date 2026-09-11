#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
The stand for code2zfl. Three kinds of control, and all three are needed:

  POSITIVE   planted injections must come back REFUTED — an instrument that
             cannot see a known-present instance has no right to report absence;
  NEGATIVE   clean code must come back EARNED, opaque code OPEN;
  VACUITY    with the sanitizer catalog emptied, f02 must flip to OPEN (unknown fn = Z), and
             with the source catalog emptied, f01 must flip to OPEN — proving the
             catalog is load-bearing and the verdicts are not the frame talking.

Run:  CODE2ZFL_AUTOLOAD=/path/to/vendor/autoload.php python3 test_code2zfl.py
"""
import json
import os
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import code2zfl  # noqa: E402

FIX = os.path.join(HERE, "fixtures")
OVERLAY = os.path.join(FIX, "overlay-wrapper.json")
LARAVEL = os.path.join(HERE, "overlays", "laravel.json")
AUTOLOAD = os.environ.get("CODE2ZFL_AUTOLOAD")

EXPECT = {
    "f01_plain_injection.php": ["REFUTED"],
    "f02_intval.php": ["EARNED"],
    "f03_escaped_quoted.php": ["EARNED"],
    "f04_escaped_unquoted.php": ["REFUTED"],
    "f05_wrong_context.php": ["REFUTED"],
    "f06_opaque.php": ["OPEN"],
    "f07_constant.php": ["EARNED", "EARNED"],
    "f08_branch.php": ["REFUTED"],
    "f09_loop.php": ["REFUTED"],
    "f10_wrapper.php": ["EARNED"],
    "f11_param.php": ["OPEN"],
    "f12_transform_drops_sanitization.php": ["REFUTED"],
    "f13_reassigned_clean.php": ["EARNED"],
    "f14_broken.php": "E",
    "f15_server_keys.php": ["EARNED", "REFUTED"],
    "f16_like_pattern.php": ["EARNED"],
    "f17_unknown_part.php": ["EARNED", "OPEN"],
    "f18_explode_implode.php": ["EARNED"],
    "f19_raw_part_beside_unknown.php": ["REFUTED"],
    "f20_header_redirect.php": ["REFUTED"],
    "f21_dynamic_class.php": ["REFUTED"],
    "f22_param_from_caller.php": ["REFUTED"],
    "f23_property_across_methods.php": ["REFUTED"],
    "f24_callee_sanitizes.php": ["EARNED"],
    "f25_return_carries_taint.php": ["REFUTED"],
    "f26_query_built_in_pieces.php": ["EARNED", "EARNED", "EARNED"],
    "f27_same_method_name_two_objects.php": ["EARNED", "REFUTED"],
    "f28_guard_in_array.php": ["EARNED", "OPEN"],
    "f29_guard_early_exit.php": ["EARNED"],
    "f30_guard_preg_match.php": ["EARNED", "REFUTED"],
    "f31_html.php": ["REFUTED", "EARNED", "REFUTED"],
    "f32_header.php": ["REFUTED", "EARNED"],
    "f33_callable_whitelist.php": ["EARNED", "EARNED", "REFUTED"],
    "f34_filter_var.php": ["EARNED"],
    "f35_laravel_raw.php": ["REFUTED", "EARNED", "REFUTED"],
    "f36_laravel_identifier.php": ["REFUTED", "EARNED", "EARNED"],
    # 2026-09-09 — from the SARD/Stivalet suite (42k files) and DVWA
    "f37_sprintf_format.php": ["EARNED", "EARNED", "REFUTED", "REFUTED"],
    "f38_settype.php": ["EARNED"],
    "f39_guard_wrapped_and_once_assigned.php": ["EARNED", "EARNED", "EARNED", "OPEN"],
    "f40_filter_var_guard.php": ["EARNED", "EARNED", "REFUTED", "EARNED", "REFUTED"],
    "f41_preg_replace_strip.php": ["EARNED", "REFUTED"],
    "f42_unknown_call_is_z.php": ["OPEN", "EARNED"],
    "f43_array_literal_keys.php": ["OPEN", "REFUTED", "REFUTED"],
    "f44_unknown_part_unquoted.php": ["OPEN", "EARNED"],
    "f45_guard_on_array_element.php": ["EARNED", "REFUTED"],
    "f46_equals_literal_through_preserving.php": ["EARNED", "REFUTED"],
    "f47_guard_credits_derived_value.php": ["EARNED", "REFUTED", "REFUTED"],
    "f48_html_subcontexts.php": ["EARNED", "EARNED", "REFUTED", "EARNED", "REFUTED", "EARNED", "REFUTED", "EARNED", "EARNED", "REFUTED", "EARNED", "REFUTED", "REFUTED", "EARNED"],
    "f49_html_stream_and_fragments.php": ["EARNED", "REFUTED", "REFUTED", "EARNED"],
    "f50_html_unknown_position.php": ["EARNED", "EARNED", "EARNED", "EARNED"],
    "f51_script_encoder.php": ["EARNED", "REFUTED", "EARNED"],
    "f52_files_keys.php": ["EARNED", "REFUTED"],
    "f53_substituted_joined_with_unknown.php": ["EARNED", "OPEN", "EARNED"],
    "f54_stored_input.php": ["OPEN", "EARNED", "OPEN", "EARNED", "OPEN", "EARNED", "OPEN", "EARNED", "OPEN", "OPEN"],
    "f55_object_in_file.php": ["REFUTED", "REFUTED", "REFUTED", "EARNED", "REFUTED"],
    "f56_in_file_wrapper_is_still_a_sink.php": ["REFUTED", "REFUTED"],
    "f57_setcookie_value.php": ["REFUTED", "EARNED"],
    "f58_unknown_guard.php": ["OPEN", "OPEN", "REFUTED"],
    "f59_fixed_alphabet_encoder.php": ["EARNED", "EARNED", "REFUTED"],
    "f60_isset_literal_map.php": ["EARNED", "REFUTED"],
    "f61_url_attr_after_query.php": ["EARNED", "REFUTED", "EARNED"],
    "f62_url_encoded_into_url_sink.php": ["OPEN", "OPEN", "REFUTED", "OPEN"],
    "f63_guard_on_superglobal_slot.php": ["EARNED", "REFUTED"],
    "f64_files_fields.php": ["EARNED", "REFUTED"],
    "f65_whitelist_from_a_call.php": ["OPEN", "EARNED", "REFUTED"],
    "f66_existence_is_not_a_constraint.php": ["REFUTED", "REFUTED", "REFUTED", "EARNED", "OPEN"],
    "f67_singleton_through_a_property.php": ["EARNED", "EARNED", "REFUTED"],
    "f68_unknown_check_on_a_slot.php": ["OPEN", "OPEN", "EARNED", "REFUTED"],
    "f69_first_class_callable.php": ["REFUTED"],
    "f70_property_element_slots.php": ["EARNED", "REFUTED", "REFUTED", "REFUTED"],
    "f71_not_sink_by_receiver.php": ["REFUTED"],
    "f72_self_assignment_adds_nothing.php": ["EARNED", "REFUTED"],
    "f73_preg_match_captures.php": ["REFUTED", "EARNED", "REFUTED", "EARNED"],
    "f74_preg_replace_keeps_an_alphabet.php": ["EARNED", "EARNED", "REFUTED", "REFUTED", "REFUTED"],
    "f75_isset_on_a_map_we_cannot_read.php": ["OPEN", "EARNED", "REFUTED", "OPEN", "REFUTED"],
    "f76_array_map_with_a_literal_callback.php": ["EARNED", "EARNED", "EARNED", "OPEN", "EARNED", "REFUTED", "REFUTED"],
    "f77_ternary_condition_guards_its_branches.php": ["EARNED", "EARNED", "OPEN", "REFUTED"],
    "f78_array_key_slots.php": ["REFUTED", "EARNED", "REFUTED", "REFUTED"],
    "f79_implode_delimiter_quote_parity.php": ["EARNED", "EARNED", "REFUTED", "REFUTED"],
    "f80_reject_if_outside_a_class.php": ["EARNED", "REFUTED", "REFUTED"],
    "f81_unread_position_is_not_the_friendliest.php": ["OPEN", "EARNED", "EARNED"],
    "f82_ent_flags_decide_which_quote.php": ["REFUTED", "REFUTED", "EARNED", "EARNED", "EARNED", "REFUTED", "EARNED"],
    "f83_url_encoding_does_not_reach_a_script.php": ["EARNED", "REFUTED", "REFUTED", "REFUTED", "REFUTED"],
    "f84_a_declared_property_settles_itself_only.php": ["EARNED", "REFUTED", "OPEN"],
    "f85_the_email_filter_keeps_the_single_quote.php": ["EARNED", "EARNED", "REFUTED", "REFUTED", "REFUTED"],
    "f90_a_check_does_not_outlive_its_branch.php": ["EARNED", "REFUTED", "EARNED", "EARNED", "REFUTED"],
    "f86_a_removal_closes_one_position.php": ["EARNED", "REFUTED", "EARNED", "REFUTED", "EARNED", "REFUTED"],
    "f87_sanitize_text_field_is_body_text.php": ["OPEN", "OPEN", "OPEN", "OPEN"],
    "f88_a_header_is_split_by_a_newline_only.php": ["OPEN"] * 6,
    "f89_a_call_can_carry_danger_in_several_arguments.php": ["REFUTED", "REFUTED", "REFUTED", "REFUTED", "REFUTED", "EARNED", "OPEN", "EARNED"],
    "f97_a_computed_key_may_be_any_key.php": ["REFUTED", "EARNED", "EARNED", "REFUTED"],
}
STORED = os.path.join(HERE, "overlays", "stored-input.json")
WORDPRESS = os.path.join(HERE, "overlays", "wordpress.json")


def dispositions(out):
    got = {}
    for f in out["files"]:
        name = os.path.basename(f["file"])
        got[name] = "E" if f["parse_error"] else [s["disposition"] for s in f["sinks"]]
    return got


def inheritance_probe(failures):
    """A method call resolves to the definition that actually runs, which may sit in a parent class
    in another file. Without the chain the child's sanitizer is invisible and the query reads raw."""
    out = code2zfl.run([os.path.join(FIX, "xinherit")], [], "all", AUTOLOAD)
    got = [s["disposition"] for f in out["files"] if os.path.basename(f["file"]) == "child.php" for s in f["sinks"]]
    if got != ["EARNED", "REFUTED"]:
        failures.append(f"xinherit/child.php: expected ['EARNED', 'REFUTED'], got {got}")


def ambiguous_parent_probe(failures):
    """ONE BARE CLASS NAME, TWO PARENTS. The tree-wide map cannot answer, and the answer must not depend on
    how the files were split into batches: the `extends` written in the file being judged decides. Measured
    2026-09-10 on dolibarr, where Reader\\Csv and Writer\\Csv collide and 7 sinks appeared or vanished with
    --jobs. Run at three batch counts on purpose."""
    for jobs in (1, 2, 4):
        out = code2zfl.run([os.path.join(FIX, "xambig")], [], "all", AUTOLOAD, jobs=jobs)
        for name, exp in (("reader.php", ["EARNED"]), ("writer.php", ["REFUTED"])):
            got = [s["disposition"] for f in out["files"] if os.path.basename(f["file"]) == name for s in f["sinks"]]
            if got != exp:
                failures.append(f"xambig/{name} at --jobs {jobs}: expected {exp}, got {got}")


def duplicate_class_probe(failures):
    """A CLASS DECLARED TWICE: only one copy is loaded, and neither file's text says which. The verdicts
    stand for the code as written — and the ledger has to SAY that it did not establish whether this copy
    runs. Measured 2026-09-10: 40 of 779 REFUTED across five corpora sit in such a file, zurmo's
    `eval($_GET)` among them, in the second copy of a framework whose live core has no eval."""
    out = code2zfl.run([os.path.join(FIX, "xdup")], [OVERLAY], "all", AUTOLOAD)
    for name, exp in (("legacy/Thing.php", "REFUTED"), ("live/Thing.php", "EARNED")):
        base = os.path.basename(name)
        got = [(f.get("dup_classes"), [s["disposition"] for s in f["sinks"]])
               for f in out["files"] if f["file"].endswith(name.replace("/", os.sep))]
        if len(got) != 1:
            failures.append(f"xdup/{name}: expected one file record, got {len(got)}"); continue
        dup, disp = got[0]
        if disp != [exp]:
            failures.append(f"xdup/{name}: expected ['{exp}'], got {disp}")
        if not dup or dup[0]["files"] != 2:
            failures.append(f"xdup/{name}: the duplicate class was NOT named — dup_classes={dup}")
    # and it must reach the human summary, not only the json
    md = code2zfl.summary_md(out)
    if "declared TWICE" not in md:
        failures.append("xdup: the duplicate class is in the json and NOT in the human summary")


def include_probe(failures):
    """A front controller guards the request once; every page that requires it is judged under that
    guard — where it DOMINATES: a check inside a branch that does not leave guards nothing after it (f90).
    Without the include graph p and q read as plain refutations; with the old file-wide guard map s read as clean."""
    out = code2zfl.run([os.path.join(FIX, "xinclude")], [], "all", AUTOLOAD)
    got = [s["disposition"] for f in out["files"] if os.path.basename(f["file"]) == "page.php" for s in f["sinks"]]
    if got != ["OPEN", "EARNED", "REFUTED", "REFUTED"]:
        failures.append(f"xinclude/page.php: expected ['OPEN', 'EARNED', 'REFUTED', 'REFUTED'], got {got}")


def cross_file_probe(failures):
    """Cross-file sight: pass 1 learns the callees in lib.php, pass 2 judges app.php with them.
    Without it, all four are OPEN (the calls are opaque) and the sink inside lib.php is invisible
    from app.php entirely."""
    out = code2zfl.run([os.path.join(FIX, "xfile")], [], "all", AUTOLOAD)
    got = [s["disposition"] for f in out["files"] if os.path.basename(f["file"]) == "app.php" for s in f["sinks"]]
    want = ["REFUTED", "EARNED", "OPEN", "REFUTED"]
    if got != want:
        failures.append(f"xfile/app.php: expected {want}, got {got}")
    flat = code2zfl.run([os.path.join(FIX, "xfile")], [], "all", AUTOLOAD, cross=False)
    got2 = [s["disposition"] for f in flat["files"] if os.path.basename(f["file"]) == "app.php" for s in f["sinks"]]
    if got2 == want:
        failures.append("xfile: --no-cross gives the same answer, so the probe does not test cross-file sight")


def any_probe(failures):
    """Thirteen parameters, past the per-parameter limit (xany): the summary answers for all of them at once as
    passes ["any"]. Request data carried through such a function must stay request data; before 2026-09-11 the judge
    matched only the argument's own index and read it as "constants only" - a false EARNED on dolibarr's img_picto."""
    out = code2zfl.run([os.path.join(FIX, "xany")], [], "all", AUTOLOAD)
    got = [(s["line"], s["disposition"]) for f in out["files"] if os.path.basename(f["file"]) == "page.php" for s in f["sinks"]]
    want = [(4, "OPEN"), (5, "EARNED"), (6, "EARNED")]
    if got != want:
        failures.append(f"xany/page.php: expected {want} (unknown / substituted / constant), got {got}")


def own_probe(failures):
    """What a function produces BY ITSELF (xown): f() and g() return request data whatever they are given, k() returns it
    escaped; h()'s include takes its OWN $_GET, so neither call of h() is the argument's sink. Before 2026-09-11 the summary
    described arguments only: echo f('c') and echo g() read EARNED, and h($_GET['z']) was accused of h's own flaw."""
    out = code2zfl.run([os.path.join(FIX, "xown")], [], "all", AUTOLOAD)
    got = [(s["line"], s["disposition"]) for f in out["files"] if os.path.basename(f["file"]) == "page.php" for s in f["sinks"]]
    want = [(2, "OPEN"), (3, "OPEN"), (6, "EARNED"), (7, "EARNED"), (8, "REFUTED")]  # own source = unknown, not accusation
    if got != want:
        failures.append(f"xown/page.php: expected {want}, got {got}")


def main():
    failures = []
    out = code2zfl.run([FIX], [OVERLAY, LARAVEL], "all", AUTOLOAD, cross=False)
    got = dispositions(out)
    for name, exp in EXPECT.items():
        if got.get(name) != exp:
            failures.append(f"{name}: expected {exp}, got {got.get(name)}")
    # every fixture in the folder is in the table — an unlisted fixture is an untested claim
    probed = {os.path.basename(f["file"]) for f in out["files"] if os.sep + "xfile" + os.sep in f["file"] or os.sep + "xinherit" + os.sep in f["file"] or os.sep + "xany" + os.sep in f["file"] or os.sep + "xown" + os.sep in f["file"] or os.sep + "xinclude" + os.sep in f["file"] or os.sep + "xconflict" + os.sep in f["file"] or os.sep + "xambig" + os.sep in f["file"] or os.sep + "xdup" + os.sep in f["file"]}
    for name in got:
        if name not in EXPECT and name not in probed:                  # the cross-file pairs are asserted by their own probes
            failures.append(f"{name}: fixture without an expectation")
    # weak links are NAMED on OPEN
    for f in out["files"]:
        for s in f["sinks"]:
            if s["disposition"] == "OPEN" and not s["weak"]:
                failures.append(f"{os.path.basename(f['file'])}: OPEN without a named weak link")

    # ---- VACUITY controls: the catalog must be load-bearing
    base = json.load(open(os.path.join(HERE, "catalog.json"), encoding="utf-8"))
    with tempfile.TemporaryDirectory() as td:
        nosan = dict(base); nosan["sanitizers"] = {"functions": {}, "methods": {}, "casts": {}}
        p1 = os.path.join(td, "nosan.json"); json.dump(nosan, open(p1, "w"))
        g1 = dispositions(code2zfl.run([os.path.join(FIX, "f02_intval.php")], [], "sql", AUTOLOAD, catalog=p1))
        # an unlisted function is UNKNOWN, hence Z, hence OPEN — the sanitizer entry is what
        # turns OPEN into EARNED; if f02 stayed EARNED the catalog would be decoration
        if g1.get("f02_intval.php") != ["OPEN"]:
            failures.append(f"vacuity/sanitizers: f02 with no sanitizers should be OPEN, got {g1}")
        nosrc = dict(base); nosrc["sources"] = {"superglobals": [], "functions": []}
        p2 = os.path.join(td, "nosrc.json"); json.dump(nosrc, open(p2, "w"))
        g2 = dispositions(code2zfl.run([os.path.join(FIX, "f01_plain_injection.php")], [], "sql", AUTOLOAD, catalog=p2))
        if g2.get("f01_plain_injection.php") != ["OPEN"]:
            failures.append(f"vacuity/sources: f01 with no sources should be OPEN, got {g2}")

    # ---- a WordPress sanitizer guarantees exactly what its SOURCE says and no more: sanitize_text_field
    # takes every raw '<' out and leaves the quotes alone, so it is body text and nothing else. The fixture
    # runs under the WordPress overlay, where the function is declared, and its four sinks are the four
    # positions: body text earns, both attribute kinds and a quoted SQL string do not.
    g4 = dispositions(code2zfl.run([os.path.join(FIX, "f87_sanitize_text_field_is_body_text.php")],
                                   [OVERLAY, WORDPRESS], "all", AUTOLOAD))
    if g4.get("f87_sanitize_text_field_is_body_text.php") != ["EARNED", "REFUTED", "REFUTED", "REFUTED"]:
        failures.append(f"wordpress overlay: f87 should be EARNED then three REFUTED, got {g4}")

    # ---- a header is split by a NEWLINE and by nothing else, and that is weaker than what a URL attribute
    # asks. `crlf-free` must reach the cookie sink and must NOT reach `href="` with an open scheme, or
    # `javascript:` walks in. sanitize_textarea_field keeps newlines, so not even the cookie.
    g5 = dispositions(code2zfl.run([os.path.join(FIX, "f88_a_header_is_split_by_a_newline_only.php")],
                                   [OVERLAY, WORDPRESS], "all", AUTOLOAD))
    exp5 = ["EARNED", "REFUTED", "REFUTED", "REFUTED", "REFUTED", "EARNED"]
    if g5.get("f88_a_header_is_split_by_a_newline_only.php") != exp5:
        failures.append(f"wordpress overlay: f88 should be {exp5}, got {g5}")

    # ---- the stored-input overlay turns what was stored into a SOURCE: f54 must flip from five OPEN to five REFUTED
    g3 = dispositions(code2zfl.run([os.path.join(FIX, "f54_stored_input.php")], [OVERLAY, STORED], "sql", AUTOLOAD))
    if g3.get("f54_stored_input.php") != ["REFUTED"] * 5:
        failures.append(f"stored-input overlay: f54 should be five REFUTED, got {g3}")

    cross_file_probe(failures)
    inheritance_probe(failures)
    ambiguous_parent_probe(failures)
    duplicate_class_probe(failures)
    include_probe(failures)
    any_probe(failures)
    own_probe(failures)
    # ---- a NAME defined differently in two files is a conflict (unknown), not "the last one wins"; and a method
    # summary is never read for a receiver that is not $this (b.php: $db->safe() inside XcA must not be XcA::safe)
    xc = code2zfl.run([os.path.join(FIX, "xconflict")], [], "all", AUTOLOAD)
    got = {os.path.basename(f["file"]): [s["disposition"] for s in f["sinks"]] for f in xc["files"]}
    if got.get("app.php") != ["OPEN"]:
        failures.append(f"xconflict/app.php: conflicting xc_clean() must read as unknown -> OPEN, got {got.get('app.php')}")
    if "EARNED" in got.get("b.php", []):
        failures.append(f"xconflict/b.php: $db->safe() credited with XcA::safe -> {got.get('b.php')}")
    n = sum(len(v) if isinstance(v, list) else 1 for v in EXPECT.values()) + 5
    if failures:
        print("FAIL")
        for x in failures:
            print("  -", x)
        sys.exit(1)
    print(f"PASS: {n} sink verdicts as expected across {len(EXPECT)} fixtures + the cross-file, conflict, inheritance, ambiguous-parent, duplicate-class and include pairs (+ f54 under stored-input, f87 and f88 under wordpress) + 2 vacuity controls")


if __name__ == "__main__":
    main()
