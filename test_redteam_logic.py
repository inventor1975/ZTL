# -*- coding: utf-8 -*-
"""
test_redteam_logic — the logic core against its own definitions (2026-09-27).

A red-team stand, NOT registered in run_all.py (registration changes the counted
stands; decided in review). Every expectation comes from an independent oracle,
`inventory/probes/redteam_logic_oracle.py`, written from the documents (SPEC.md,
the docstrings of zverify / ztljudge / zpassport, lean/*.lean) and importing
none of the code under test.

Findings pinned — each check below FAILS on master @ 99f8592 and names what
disagrees with what:

  L1  CODE. `ztljudge._lazy` reads the CONSTANTS T and F as unverified marks
      (its leaf case is `m.get(phi, Z)`, and a constant is never in the
      marking). `F` has lazy value Z and "pending ['F']"; `T | p` is EARNED yet
      lazy Z, pending ['T', 'p']. Strong Kleene — the register the docstring
      names, and Lean's `labF` over `top`/`bot` — decides both. Reaches the
      studio: `x > 1 | T` reports disposition EARNED with lazy "Z".
  L2  DOCUMENTS vs CODE. ONBOARDING §1 and ztl.py: "verdicts are always
      two-valued" (T or F). An ATOMIC claim's verdict is Z: judge("p") gives
      verdict Z. The generating principle bars Z from COMPOUNDS only, so the
      code follows the principle and the sentence overstates it — or the judge
      should refuse/translate atomic claims. Which side moves is the curator's
      call; the check pins the disagreement.
  L3  DOCUMENTS. CLASSIC-VS-ZTL.md ("the same 588 validities of the depth-≤2
      pool, the same set element for element"), the preprint and
      paper/core_logic_checks.py count 588 on a 2926-entry pool that lists 20
      formulas twice; as a SET the pool has 2906 formulas and 584 validities —
      which is what zledger.py and the card's own schedule table (584 / 584)
      say. 588 = 588 still holds; "the set" has 584 elements.

Then a seeded sweep over every section of the search (evaluation, parser,
grades with budgets, judge, passports, laws): a disagreement that is not L1 is a
NEW finding and fails the stand by itself.

Run: python3 test_redteam_logic.py  ->  REDTEAM LOGIC GREEN (nothing found)
     exits 1 and names every finding otherwise.
"""
import os
import random
import re
import sys
import time
from itertools import product

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "inventory", "probes"))

import redteam_logic_oracle as O                     # noqa: E402
import ztl                                           # noqa: E402
import zverify                                       # noqa: E402
import ztljudge                                      # noqa: E402
import zpassport                                     # noqa: E402

CHECKS, FAILS = 0, []


def check(cond, what):
    global CHECKS
    CHECKS += 1
    if not cond:
        FAILS.append(what)
        print(f"FAIL: {what}")


t0 = time.time()

# ------------------------------------------------------------------ L1
for text, marks in (("F", {}), ("T | p", {}), ("F & p", {"p": "T"}), ("p & F", {})):
    phi = ztljudge.formalize(text)
    kern = {a: marks.get(a, "Z") for a in O.atoms(phi)}
    want = O.ev_lazy(phi, kern)
    r = ztljudge.judge(text, marks)
    check(r["lazy"] == want,
          f"L1 lazy register of {text!r} {marks}: code {r['lazy']}, strong Kleene {want}")
    check(not set(r["pending"]) & {"T", "F", "Z"},
          f"L1 pending of {text!r} names a CONSTANT as a ground: {r['pending']}")
try:
    import zfl
    rep = zfl.run({"claim": "x > 1 | T", "rows": [
        {"name": "x", "means": "x", "status": "unverified", "value": "[0,5]"}]})
    num = rep["report"]["numeric"]
    check(not (num["disposition"] == "EARNED" and num["lazy"] == "Z"),
          f"L1 via zfl.run: `x > 1 | T` is {num['disposition']} with lazy {num['lazy']}")
except Exception as e:                                # noqa: BLE001
    check(False, f"L1 via zfl.run raised {e!r}")

# ------------------------------------------------------------------ L2
# RESOLVED 2026-09-27 on the DOCUMENTS' side (the curator's choice): the principle bars Z
# from compounds only, and so do the documents now. Pinned both ways: a single unverified
# atom answers Z; a compound never does; no living document says "verdicts are always".
r = ztljudge.judge("p", {})
check(r["verdict"] == "Z" and r["disposition"] == "OPEN",
      f"L2 a claim that is one unverified atom answers Z / OPEN: got {r['verdict']} / {r['disposition']}")
for text in ("p & q", "p | ~p", "p -> q", "~p", "p ^ q", "p = q", "~~p"):
    r = ztljudge.judge(text, {})
    check(r["verdict"] in ("T", "F"), f"L2 compound {text!r} must be two-valued: got {r['verdict']}")
for doc in ("ONBOARDING.md", "SPEC.md", "README.md", "ztl.py"):
    txt = open(os.path.join(HERE, doc), encoding="utf-8").read().lower()
    check("verdicts are always t or f" not in txt and "verdicts are always two-valued" not in txt
          and "verdicts are always\ntwo-valued" not in txt,
          f"L2 {doc} still says verdicts are ALWAYS two-valued; the principle says compounds")

# ------------------------------------------------------------------ L3
BIN = ["and", "or", "imp", "xor", "xnor"]
d1 = ["p", "q"] + [("not", x) for x in ("p", "q")] + \
     [(o, a, b) for o in BIN for a in ("p", "q") for b in ("p", "q")]
d2 = [(o, a, b) for o in BIN for a in d1 for b in d1] + \
     [("not", x) for x in d1 if not isinstance(x, str)]
pool = d1 + d2
taut = [f for f in set(pool) if all(O.ev(f, {"p": a, "q": b}) == "T" for a in "TF" for b in "TF")]
card = open(os.path.join(HERE, "CLASSIC-VS-ZTL.md"), encoding="utf-8").read()
m = re.search(r"same (\d+) validities of the depth-≤2 pool", card)
quoted = int(m.group(1)) if m else None
check(quoted == len(taut),
      f"L3 CLASSIC-VS-ZTL.md quotes {quoted} validities of the depth-≤2 pool "
      f"'the same set'; the set has {len(taut)} (the 2926-entry list repeats "
      f"{len(pool) - len(set(pool))} formulas, 4 of them tautologies)")

# ------------------------------------------------------------------ sweep
rnd = random.Random("stand:20260927")
ATOMS = [f"p{i}" for i in range(10)]
new = []

# tables and anchors
for x in O.VALS:
    if ztl.NOT(x) != O.TABLE1[x]:
        new.append(("table not", x))
    for y in O.VALS:
        for op in O.OPS:
            if ztl.OPS2[op](x, y) != O.TABLE2[op][(x, y)]:
                new.append(("table", op, x, y))

# evaluation, deep chains included
for _ in range(60000):
    ats = ATOMS[:rnd.randint(1, 10)]
    phi = O.random_formula(rnd, rnd.randint(0, 6), ats)
    env = {a: rnd.choice(O.VALS) for a in ats}
    if ztl.ev(phi, env) != O.ev(phi, env):
        new.append(("ev", ztl.show(phi), env))
chain = "p0"
for i in range(3000):
    chain = (O.OPS[i % 5], chain, ATOMS[i % 10])
env = {a: rnd.choice(O.VALS) for a in ATOMS}
if ztl.ev(chain, env) != O.ev(chain, env):
    new.append(("ev deep chain",))

# grades, budgets, foreign marks
WEAKER = {"hereditary": {"hereditary", "sound-or-better", "undetermined"},
          "sound": {"sound", "sound-or-better", "undetermined"},
          "until-verification": {"until-verification", "undetermined"}}
for _ in range(15000):
    ats = ATOMS[:rnd.randint(1, 6)]
    phi = O.random_formula(rnd, rnd.randint(0, 5), ats)
    env = {a: rnd.choice(("T", "F", "Z", "Z")) for a in ats}
    mk = {a: ("M" if v == "Z" else v) for a, v in env.items()}
    want = O.grade(phi, env)
    b = rnd.choice([1, 3, 9, 27, 81])
    if (zverify.grade(phi, mk) != want
            or zverify.grade(phi, mk, budget=b) not in WEAKER[want]
            or zverify.grade(phi, {**mk, "x0": "M", "x1": "M"}) != want):
        new.append(("grade", ztl.show(phi), env))


# the Lean negFree, transcribed from lean/ContextClosure.lean
def lean_occurs(a, f):
    return f == a if isinstance(f, str) else any(lean_occurs(a, c) for c in f[1:])


def lean_negfree(a, f):
    if isinstance(f, str):
        return True
    if f[0] == "not":
        return not lean_occurs(a, f[1])
    if f[0] in ("xor", "xnor"):
        return not (lean_occurs(a, f[1]) or lean_occurs(a, f[2]))
    if f[0] == "imp":
        return (not lean_occurs(a, f[1])) and lean_negfree(a, f[2])
    return lean_negfree(a, f[1]) and lean_negfree(a, f[2])


for _ in range(5000):
    phi = O.random_formula(rnd, rnd.randint(0, 5), ATOMS[:4])
    for a in ATOMS[:4]:
        if zverify.neg_free(a, phi) != lean_negfree(a, phi):
            new.append(("negFree", ztl.show(phi), a))

# judge: everything except the L1 column on claims with constants
for _ in range(8000):
    ats = ATOMS[:rnd.randint(1, 6)]
    phi = O.random_formula(rnd, rnd.randint(1, 5), ats)
    text = O.text_full(phi)
    marks = {a: rnd.choice(["T", "F", "Z", "E"]) for a in ats if rnd.random() < 0.6}
    r = ztljudge.judge(text, marks)
    full = {a: marks.get(a, "Z") for a in O.atoms(phi)}
    kern = {a: ("Z" if v == "E" else v) for a, v in full.items()}
    v, g = O.ev(phi, kern), O.grade(phi, kern)
    unv = sorted(a for a, x in full.items() if x == "Z")
    gone = sorted(a for a, x in full.items() if x == "E")
    has_const = bool(set(re.findall(r"\b[TFZ]\b", text)))
    wrong = []
    if ztljudge.formalize(text) != phi:
        wrong.append("parse")
    if (r["verdict"], r["grade"], r["unverified"], r["absent"]) != (v, g, unv, gone):
        wrong.append("verdict/grade/unverified")
    if r["disposition"] != O.disposition(v, g, unv, gone):
        wrong.append("disposition")
    if r["lazy"] != O.ev_lazy(phi, kern) and not has_const:
        wrong.append("lazy")
    if wrong:
        new.append(("judge", text, marks, wrong))

# passports, catalogue and parity
for _ in range(4000):
    names = [f"s{i}" for i in range(rnd.randint(1, 4))]
    system = {s: O.random_formula(rnd, rnd.randint(0, 3), names + ["T", "F", "Z"], 0.0)
              for s in names}
    lfp, kind = O.passports(system)
    lfp2, _, ck = zpassport.passports(system)
    if lfp2 != lfp or {s: ck[s] for s in names} != kind:
        new.append(("passport", system))

for rec in new[:20]:
    check(False, f"NEW disagreement: {rec}")
check(not new, f"the seeded sweep found {len(new)} disagreements outside L1")
print(f"  sweep done in {time.time() - t0:.0f} s")

if FAILS:
    print(f"REDTEAM LOGIC RED: {len(FAILS)} of {CHECKS} checks fail — see above")
    sys.exit(1)
print(f"REDTEAM LOGIC GREEN ({CHECKS} checks)")
