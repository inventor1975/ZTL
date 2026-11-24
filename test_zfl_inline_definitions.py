# -*- coding: utf-8 -*-
"""test_zfl_inline_definitions — a defined row (or a cycle of them) must not identify the occurrences of a dirty atom
(2026-11-24).

Before the fix, zfl.run handed the judge a defined row as the passport's stable-step value, so `safe := ~ok | ok` with
`ok` unverified came back EARNED "grounded outright"; the same formula as the claim is EARNED IF STABLE. Each check
below is the claim-as-formula verdict, which the defined-row path must now equal; plus the cases that must NOT move
(a Tr(...) definition, a self-referential system, rows of verified marks, the book's chapter 03).
"""
import zfl

ok = {"name": "ok", "status": "unverified", "means": "a value that is not ours"}
fails = []


def disp(rows, claim):
    r = zfl.run({"rows": rows, "claim": claim})
    assert r.get("ok", True), r.get("issues")
    return r["report"]["judge"]["disposition"]


def check(name, got, want):
    if got != want:
        fails.append(f"{name}: got {got}, want {want}")


for g, want in [("~ok | ok", "EARNED IF STABLE"), ("ok & ~ok", "REFUTED IF STABLE"), ("~(ok & ~ok)", "EARNED IF STABLE"),
                ("ok -> ok", "EARNED IF STABLE"), ("~~ok", "ON CREDIT"), ("ok", "OPEN")]:
    rows = [ok, {"name": "safe", "status": "defined", "ground": g, "means": "m"}]
    check(f"defined {g}", disp(rows, "safe"), want)
    check(f"claim {g} (reference)", disp([ok], g), want)

# two defined rows sharing the dirty atom: the identification across rows is not free either
rows = [ok, {"name": "a", "status": "defined", "ground": "ok", "means": "m"},
        {"name": "b", "status": "defined", "ground": "~ok", "means": "m"}]
check("a | b across rows", disp(rows, "a | b"), "EARNED IF STABLE")
# nested definitions
rows = [ok, {"name": "a", "status": "defined", "ground": "ok", "means": "m"},
        {"name": "c", "status": "defined", "ground": "a | ~a", "means": "m"}]
check("nested c := a | ~a", disp(rows, "c"), "EARNED IF STABLE")
# must NOT move: Tr reads Z as F at each occurrence already
rows = [ok, {"name": "safe", "status": "defined", "ground": "Tr(ok) | ~Tr(ok)", "means": "m"}]
check("Tr definition unchanged", disp(rows, "safe"), "EARNED")
# must NOT move: a self-referential system stays with the passport
check("liar stays with the passport", disp([{"name": "L", "status": "defined", "ground": "~L", "means": "liar"}], "L"), "OPEN")
# must NOT move: definitions over verified rows (the book's chapter 03 shape, the 2026-08-28 fix)
rows = [{"name": "v", "status": "verified", "ground": "act", "means": "m"},
        {"name": "w", "status": "refuted", "ground": "act", "means": "m"},
        {"name": "d1", "status": "defined", "ground": "v", "means": "m"},
        {"name": "d2", "status": "defined", "ground": "w", "means": "m"}]
check("verified definitions unchanged", disp(rows, "d1 & ~d2"), "EARNED")
# the inlined claim is reported
r = zfl.run({"rows": [ok, {"name": "safe", "status": "defined", "ground": "~ok | ok", "means": "m"}], "claim": "safe"})
check("claim_inlined reported", r["report"]["judge"].get("claim_inlined"), "(~ok | ok)")

# cycles (2026-11-24, second step): a dirty input repeated inside a self-referential system
D = lambda n, g: {"name": n, "status": "defined", "ground": g, "means": "m"}
check("cycle A := (ok | ~ok) | A", disp([ok, D("A", "(ok | ~ok) | A")], "A"), "EARNED IF STABLE")
check("cycle A := ok | B; B := ~ok | A", disp([ok, D("A", "ok | B"), D("B", "~ok | A")], "A"), "EARNED IF STABLE")
check("cycle A := (ok & ~ok) & A", disp([ok, D("A", "(ok & ~ok) & A")], "A"), "REFUTED IF STABLE")
check("cycle A := (ok & ~ok) | A (a truth-teller remains)", disp([ok, D("A", "(ok & ~ok) | A")], "A"), "OPEN")
check("cycle, one occurrence: unchanged", disp([ok, D("A", "ok & A")], "A"), "OPEN")
# self-reference with no dirty input: the passport's own business, unchanged
check("truth-teller unchanged", disp([D("T1", "T1")], "T1"), "OPEN")
check("strong liar unchanged", disp([D("S", "~S & S")], "S"), "REFUTED")

if fails:
    print("RED:", *fails, sep="\n  ")
    raise SystemExit(1)
print("INLINE DEFINITIONS GREEN — 25 checks")
