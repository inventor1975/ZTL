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
}


def dispositions(out):
    got = {}
    for f in out["files"]:
        name = os.path.basename(f["file"])
        got[name] = "E" if f["parse_error"] else [s["disposition"] for s in f["sinks"]]
    return got


def main():
    failures = []
    out = code2zfl.run([FIX], [OVERLAY], "all", AUTOLOAD)
    got = dispositions(out)
    for name, exp in EXPECT.items():
        if got.get(name) != exp:
            failures.append(f"{name}: expected {exp}, got {got.get(name)}")
    # every fixture in the folder is in the table — an unlisted fixture is an untested claim
    for name in got:
        if name not in EXPECT:
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

    n = sum(len(v) if isinstance(v, list) else 1 for v in EXPECT.values())
    if failures:
        print("FAIL")
        for x in failures:
            print("  -", x)
        sys.exit(1)
    print(f"PASS: {n} sink verdicts as expected across {len(EXPECT)} fixtures + 2 vacuity controls")


if __name__ == "__main__":
    main()
