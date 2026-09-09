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
    "f28_guard_in_array.php": ["EARNED", "REFUTED"],
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
    "f39_guard_wrapped_and_once_assigned.php": ["EARNED", "EARNED", "EARNED", "REFUTED"],
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
    "f53_substituted_joined_with_unknown.php": ["OPEN", "EARNED"],
    "f54_stored_input.php": ["OPEN", "EARNED", "OPEN", "EARNED", "OPEN", "EARNED", "OPEN", "EARNED", "OPEN", "OPEN"],
    "f55_object_in_file.php": ["REFUTED", "REFUTED", "REFUTED", "EARNED", "REFUTED"],
    "f56_in_file_wrapper_is_still_a_sink.php": ["REFUTED", "REFUTED"],
    "f57_setcookie_value.php": ["REFUTED", "EARNED"],
    "f58_unknown_guard.php": ["OPEN", "OPEN", "REFUTED"],
    "f59_fixed_alphabet_encoder.php": ["EARNED", "EARNED", "REFUTED"],
    "f60_isset_literal_map.php": ["EARNED", "REFUTED"],
    "f61_url_attr_after_query.php": ["EARNED", "REFUTED", "EARNED"],
}
STORED = os.path.join(HERE, "overlays", "stored-input.json")


def dispositions(out):
    got = {}
    for f in out["files"]:
        name = os.path.basename(f["file"])
        got[name] = "E" if f["parse_error"] else [s["disposition"] for s in f["sinks"]]
    return got


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


def main():
    failures = []
    out = code2zfl.run([FIX], [OVERLAY, LARAVEL], "all", AUTOLOAD, cross=False)
    got = dispositions(out)
    for name, exp in EXPECT.items():
        if got.get(name) != exp:
            failures.append(f"{name}: expected {exp}, got {got.get(name)}")
    # every fixture in the folder is in the table — an unlisted fixture is an untested claim
    probed = {os.path.basename(f["file"]) for f in out["files"] if os.sep + "xfile" + os.sep in f["file"] or os.sep + "xconflict" + os.sep in f["file"]}
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

    # ---- the stored-input overlay turns what was stored into a SOURCE: f54 must flip from five OPEN to five REFUTED
    g3 = dispositions(code2zfl.run([os.path.join(FIX, "f54_stored_input.php")], [OVERLAY, STORED], "sql", AUTOLOAD))
    if g3.get("f54_stored_input.php") != ["REFUTED"] * 5:
        failures.append(f"stored-input overlay: f54 should be five REFUTED, got {g3}")

    cross_file_probe(failures)
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
    print(f"PASS: {n} sink verdicts as expected across {len(EXPECT)} fixtures + the cross-file pair + the conflict pair (+ f54 under stored-input) + 2 vacuity controls")


if __name__ == "__main__":
    main()
