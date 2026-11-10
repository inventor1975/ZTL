# -*- coding: utf-8 -*-
"""test_zjudge2lean — the emitter states what the judge said, and the generated Lean file is not stale.
(Lean itself checks the statements: lean/TrolleyJudged.lean is built by run_all's Lean step.)"""
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)
sys.path.insert(0, os.path.join(_HERE, "dilemmas"))

from zjudge2lean import emit_claim, emit_file      # noqa: E402

n = 0


def check(cond, what):
    global n
    assert cond, what
    n += 1


def theorems(text):
    return sorted(l.split()[1] for l in text.splitlines() if l.startswith("theorem "))


# REFUTED IF STABLE: verdict + stable + not_outright
t, r = emit_claim("x", "((u & f) -> o) & ((dk & k) -> ~o) & u & dk & f & k", {"f": "T", "k": "T"})
check(r["disposition"] == "REFUTED IF STABLE", r["disposition"])
check(theorems(t) == ["not_outright", "stable", "verdict"], theorems(t))
# OPEN (not hereditary): both outcomes reachable
t, r = emit_claim("x", "f -> o", {"f": "T"})
check(r["disposition"] == "OPEN" and theorems(t) == ["reach_F", "reach_T", "verdict"], (r["disposition"], theorems(t)))
# EARNED with no dirty atom: only the verdict
t, r = emit_claim("x", "a & b", {"a": "T", "b": "T"})
check(r["disposition"] == "EARNED" and theorems(t) == ["verdict"], (r["disposition"], theorems(t)))
# EARNED IF STABLE where the core's own verdict under Z is F: 'stable' states the CLEANINGS' value (T)
t, r = emit_claim("x", "(a -> b) | ~b", {})
check(r["disposition"] == "EARNED IF STABLE" and r["verdict"] == "F", (r["disposition"], r["verdict"]))
check("= T := by decide" in t.split("theorem stable")[1].split("\n")[0], "stable must state T")
# EARNED, each dirty atom once: no per-occurrence statement (it would repeat 'stable')
t, r = emit_claim("x", "~(a & ~b) | c", {"c": "T"})
check(r["disposition"] == "EARNED" and theorems(t) == ["stable", "verdict"], theorems(t))
# a mark E is refused, not emitted
try:
    emit_claim("x", "a & b", {"a": "E"})
    check(False, "E accepted")
except ValueError:
    check(True, "")
# the committed Lean file is what the stand's claims generate now (no stale theorems)
import trolley                                      # noqa: E402
text, _ = emit_file(trolley.CLAIMS, title="dilemmas/trolley.py — the trolley problem's propositional verdicts")
committed = open(os.path.join(_HERE, "lean", "TrolleyJudged.lean")).read()
check(text == committed, "lean/TrolleyJudged.lean is stale: run python3 dilemmas/trolley.py --emit-lean")
print(f"ZJUDGE2LEAN GREEN ({n} checks)")
