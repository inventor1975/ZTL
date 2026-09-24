# -*- coding: utf-8 -*-
"""
test_unknown_marks — a mark the judge cannot read is refused, not read.

MEASURED 2026-09-24: ztljudge.judge("p & q", {"q": "maybe"}) and
{"q": "t"} both came back REFUTED — the string went to the connectives as
it was; "M", zverify's mark, happened to act as Z; and the file loader
dropped an unknown mark in silence, the atom going on as Z. Case does not
matter (the loader always read `t` as T); anything that is not T, F, Z or E
is refused, with a word for M.
Run: python3 test_unknown_marks.py  ->  UNKNOWN MARKS GREEN
"""
import os
import sys
import tempfile

import ztljudge

CHECKS = 0


def check(cond, what):
    global CHECKS
    CHECKS += 1
    if not cond:
        print("FAIL:", what)
        sys.exit(1)


def refused(marking):
    try:
        ztljudge.judge("p & q", marking)
    except ValueError as exc:
        return str(exc)
    return None


for bad in ("maybe", "M", "yes", "1", ""):
    said = refused({"p": "T", "q": bad})
    check(said is not None and "unknown mark" in said, f"{bad!r} is refused: {said}")
check("zverify" in refused({"p": "T", "q": "M"}), "M is refused with a word about zverify")
check(ztljudge.judge("p & q", {"p": "T", "q": "t"})["disposition"] == "EARNED", "lower-case t is T")
check(ztljudge.judge("p & q", {"p": "T", "q": "Z"})["disposition"] == "OPEN", "Z is OPEN, as before")
check(ztljudge.judge("p & q", {"p": "T", "q": "F"})["disposition"] == "REFUTED", "F refutes, as before")
with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as fh:
    fh.write("c1 :: p & q :: p=T q=maybe\n")
try:
    ztljudge.load_claims(fh.name)
    loaded = "read"
except ValueError as exc:
    loaded = str(exc)
finally:
    os.unlink(fh.name)
check("unknown mark" in loaded, f"the file loader refuses it too: {loaded}")
print(f"UNKNOWN MARKS GREEN — {CHECKS} checks")
