# -*- coding: utf-8 -*-
"""
test_redteam_numeric — the numeric judge must never give a WRONG forced verdict.

A red-team stand (2026-09-26), NOT registered in run_all.py: registration
changes the counted claims of the paper and is decided in review.

compare() says T when a claim holds under EVERY admissible reading and F when
it fails under every one; Z and E are never wrong. So only T and F are tested,
each against a reading that refutes it, computed here in exact rationals from
the semantics (inventory/probes/redteam_numeric_search.py, which imports none
of znum's evaluators).

Pinned lies — each check below FAILS on the judge of 4cc5504 and passes once
the lie is gone (the fix is decided separately; znum.py is not touched here):

  LIE-1  `sum` carries the lattice step of its LAST stepped argument once an
         unstepped one has come before it (znum._linear and znum._ev, the
         `step = s2 if step is None ...` line). sum(x, y) with x continuous and
         y int is then "on the integers", and the lattice-miss rule refutes
         sum(x, y) == 1/2 — true at x = 1/2, y = 0. Reached from the public
         document path too: zfl.run, `sum(qa,qb) == 1/2`, REFUTED.
  LIE-2  znum._real_roots skips the interval (m - ROOT_WIDTH/4, m) whenever a
         bisection midpoint m is itself a root of the derivative. A critical
         point hiding there is never a candidate, so _ev_upoly under-reports the
         maximum: a quartic claimed T (<= t) is false at x = p. Needs two
         critical points closer than 2.5e-13 — contrived, but a forced verdict
         that is wrong.

Then a seeded sweep (both modes of the search, every fragment, a few hundred
claims each): every lie it finds must be attributable to LIE-1 (re-judged with
`sum` spelled as nested `+`, the lie disappears). A lie that is not is a NEW
lie and fails the stand by itself.

Run: python3 test_redteam_numeric.py  ->  REDTEAM NUMERIC GREEN (no lie)
     exits 1 and names every lie otherwise.
"""
import os
import random
import sys
import time
from fractions import Fraction as Q

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "inventory", "probes"))

import znum                                             # noqa: E402
import zfl                                              # noqa: E402
import redteam_numeric_search as R                      # noqa: E402

CHECKS, FAILS = 0, []


def check(cond, what):
    global CHECKS
    CHECKS += 1
    if not cond:
        FAILS.append(what)
        print(f"FAIL: {what}")


def v(kind, e1, e2, qs):
    return znum.compare(kind, e1, e2, qs)[0]


def truth(kind, e1, e2, specs, reading):
    """The claim at ONE reading, from the semantics (exact rationals)."""
    x1, x2, _ = R.expand(e1, e2, specs)
    return R.gtruth(kind, x1, x2, {k: Q(val) for k, val in reading.items()})


# ------------------------------------------------------------------ LIE-1
S1 = {"x": {"lo": Q(0), "hi": Q(1), "discrete": None},
      "y": {"lo": Q(0), "hi": Q(5), "discrete": "int"}}
E1, E2 = ("sum", ["x", "y"]), Q(1, 2)
assert truth("eq", E1, E2, S1, {"x": "1/2", "y": "0"}) is True     # the witness
got = v("eq", E1, E2, R.build(S1))
check(got != "F", f"LIE-1 sum(x, y) == 1/2, x in [0,1] continuous, y in [0,5] int: "
                  f"judge {got}, true at x=1/2 y=0")
# the order matters: the stepped argument first is read correctly
check(v("eq", ("sum", ["y", "x"]), E2, R.build(S1)) != "F", "LIE-1 control: sum(y, x)")
# through the non-linear branch (_ev) as well
E1b = ("sum", [("mul", "x", "x"), "y"])
assert truth("eq", E1b, Q(1, 4), S1, {"x": "1/2", "y": "0"}) is True
got = v("eq", E1b, Q(1, 4), R.build(S1))
check(got != "F", f"LIE-1b sum(x*x, y) == 1/4 (the _ev branch): judge {got}, "
                  f"true at x=1/2 y=0")
# the public document path
DOC = {"claim": "sum(qa,qb) == 1/2", "rows": [
    {"name": "qa", "means": "qa", "status": "unverified", "value": "[0,1]"},
    {"name": "qb", "means": "qb", "status": "unverified", "value": "[0,5]",
     "scale": "int"}]}
disp = zfl.run(DOC)["report"]["numeric"]["disposition"]
check(disp != "REFUTED", f"LIE-1 via zfl.run: `sum(qa,qb) == 1/2` (qa [0,1], qb [0,5] "
                         f"scale int) -> {disp}, true at qa=1/2 qb=0")

# ------------------------------------------------------------------ LIE-2
eps = Q(1, 7 * 10 ** 12)
m = 1 - eps                  # the first bisection midpoint of [0, 2m], a root of f'
d = Q(2, 10 ** 13)           # d < ROOT_WIDTH/4: p = m - d is never looked at
p = m - d
s1, s2, s3 = p + m + 1, p * m + p + m, p * m          # f' = -(x - p)(x - m)(x - 1)


def f(x):
    x = Q(x)
    return -x ** 4 / 4 + s1 * x ** 3 / 3 - s2 * x ** 2 / 2 + s3 * x


def xpow(k):
    e = "x"
    for _ in range(k - 1):
        e = ("mul", e, "x")
    return e


F4 = ("add", ("add", ("mul", Q(-1, 4), xpow(4)), ("mul", s1 / 3, xpow(3))),
      ("add", ("mul", -s2 / 2, xpow(2)), ("mul", s3, "x")))
T4 = (f(p) + f(1)) / 2       # f(1) < T4 < f(p): the max over the box is f(p)
S2 = {"x": {"lo": Q(0), "hi": 2 * m, "discrete": None}}
assert truth("le", F4, T4, S2, {"x": str(p)}) is False              # the witness
got = v("le", F4, T4, R.build(S2))
check(got != "T", f"LIE-2 quartic <= t on [0, 2m], critical points p, m, 1 with "
                  f"m - p = 2e-13: judge {got}, false at x = {p}")

# ------------------------------------------------------------ seeded sweep
def desum(e):
    if isinstance(e, tuple):
        if e[0] == "sum":
            args = [desum(a) for a in e[1]] or [Q(0)]
            out = args[0]
            for a in args[1:]:
                out = ("add", out, a)
            return out
        if e[0] == "sqrt":
            return ("sqrt", desum(e[1]))
        return (e[0], desum(e[1]), desum(e[2]))
    return e


def attributed_to_lie1(kind, e1, e2, specs, verdict):
    """Spell every sum as nested +: same claim, same readings. If the lie
    disappears, the sum's lattice step is what told it."""
    if "sum" not in repr((e1, e2)):
        return False
    return v(kind, desum(e1), desum(e2), R.build(specs)) != verdict


t0 = time.time()
SEED, N, NP = "stand-20260926", 250, 250
found, lie1 = [], 0
for frag in list(R.FRAGMENTS) + ["doc", "docmin"]:
    rnd = random.Random(f"{frag}:{SEED}")
    grnd = random.Random(f"gold:{frag}:{SEED}")
    for i in range(N if not frag.startswith("doc") else 150):
        if frag.startswith("doc"):
            kind, e1, e2, specs = R.gen_doc(rnd)
            got, _ = R.doc_verdict(R.doc_of(kind, e1, e2, specs, rnd, minimal=frag == "docmin"))
        else:
            kind, e1, e2, specs = R.FRAGMENTS[frag](rnd)
            got, _ = R.judge(kind, e1, e2, specs)
        if got not in ("T", "F") or any(s.get("unit") for s in specs.values()):
            continue
        label, fnd = R.gold_check(kind, e1, e2, specs, got, grnd)
        if fnd is None or label == "empty" or fnd["truth"] == "undef":
            continue
        if attributed_to_lie1(kind, e1, e2, specs, got):
            lie1 += 1
        else:
            found.append((frag, got, kind, R.show(e1), R.show(e2), R.show_specs(specs),
                          fnd["reading"]))
for frag in R.PLANTED:
    rnd = random.Random(f"{frag}:{SEED}")
    made = 0
    while made < NP:
        isdoc = frag in ("p-doc", "p-docmin")
        kind, e1, e2, specs = (R.gen_doc(rnd) if isdoc else R.PLANTED[frag](rnd))
        env, variants = R.planted_variants(kind, e1, e2, specs, rnd)
        for kd, a, b, forbidden in variants:
            made += 1
            if isdoc:
                got, _ = R.doc_verdict(R.doc_of(kd, a, b, specs, rnd, minimal=frag == "p-docmin"))
            else:
                got, _ = R.judge(kd, a, b, specs)
            if got != forbidden:
                continue
            x1, x2, _ = R.expand(a, b, specs)
            assert R.gtruth(kd, x1, x2, env) is (forbidden == "F")
            if attributed_to_lie1(kd, a, b, specs, got):
                lie1 += 1
            else:
                found.append((frag, got, kd, R.show(a), R.show(b), R.show_specs(specs),
                              {k: str(x) for k, x in env.items()}))
for rec in found:
    check(False, f"NEW LIE [{rec[0]}] judge {rec[1]} on {rec[2]} {rec[3]} ~ {rec[4]} "
                 f"{rec[5]}, refuted at {rec[6]}")
check(not found, "the sweep found no lie outside LIE-1")
print(f"  sweep: {len(R.FRAGMENTS) + 2} + {len(R.PLANTED)} fragments, {lie1} lies "
      f"attributed to LIE-1, {len(found)} new; {time.time() - t0:.0f} s")

if FAILS:
    print(f"REDTEAM NUMERIC RED: {len(FAILS)} of {CHECKS} checks fail — see above")
    sys.exit(1)
print(f"REDTEAM NUMERIC GREEN ({CHECKS} checks)")
