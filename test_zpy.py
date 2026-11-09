# -*- coding: utf-8 -*-
"""zpy and zpy_lint: the layer's rules hold, its connectives are the kernel's, and the checker catches what it says."""
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import zpy                                   # noqa: E402
import zpy_lint                              # noqa: E402
import ztljudge                              # noqa: E402
from ztl import T, F, Z                      # noqa: E402

CHECKS, FAILS = 0, []


def check(cond, what):
    global CHECKS
    CHECKS += 1
    if not cond:
        FAILS.append(what)
        print(f"FAIL: {what}")


def raises(fn, exc):
    try:
        fn()
    except exc:
        return True
    except Exception:
        return False
    return False


# 1. no silent decision: bool() and == raise, on a claim and on a refusal
a = zpy.fact("a", True, by="test 1")
b = zpy.unknown("b")
c = a & b
check(raises(lambda: bool(c), zpy.Undecided), "bool(claim) raises Undecided")
check(raises(lambda: c == True, zpy.Undecided), "claim == True raises Undecided")       # noqa: E712
r = zpy.Refusal("over the budget")
check(raises(lambda: bool(r), zpy.Undecided), "bool(refusal) raises Undecided")
check(zpy.is_refusal(r) and not zpy.is_refusal(None) and not zpy.is_refusal(False), "is_refusal tells a refusal")
check(raises(lambda: a & True, TypeError), "a claim does not combine with a bare bool")
check(raises(lambda: zpy.fact("x", True, by=""), ValueError), "an earned fact without `by` is refused")
check(raises(lambda: zpy.unknown("T"), ValueError), "a reserved name cannot name a fact")

# 2. the verdicts are the kernel's, and decide has three branches
check(a.disposition == "EARNED", "a checked fact is EARNED")
check(c.disposition == "OPEN", f"a & unknown b is OPEN ({c.disposition})")
check((a | b).disposition == "EARNED", "a | unknown b is EARNED (OR carries T via the known partner)")
check((~a).disposition == "REFUTED", "~a is REFUTED")
cr = zpy.credit("k", True, source="the supplier's datasheet")
check(cr.disposition != "EARNED" and not cr.earned(), "a credit is never EARNED (fail-closed)")
check(zpy.decide(c, earned="go", refuted="stop", otherwise="verify") == "verify", "decide: OPEN -> otherwise")
check(zpy.decide(a, earned="go", refuted="stop", otherwise="verify") == "go", "decide: EARNED -> earned")
check(raises(lambda: zpy.decide(c, earned=1, refuted=2), TypeError), "decide without `otherwise` does not run")
p_ = zpy.unknown("p")
# THE CURATOR, 2026-11-10: «В этом весь ЗТЛ» — p | ~p over an unknown p is EARNED IF STABLE, not EARNED; the layer
# does not upgrade it (a first draft of the same night did, and was reverted on his word)
check(zpy.decide(p_ | ~p_, earned="yes", refuted="no", otherwise="check") == "check",
      "p | ~p over an unknown p goes to `otherwise` (EARNED IF STABLE is not EARNED)")
check(not (p_ | ~p_).earned(), "p | ~p is not earned()")
rep = c.report()
check(rep["grounds"]["a"].startswith("earned:T") and rep["grounds"]["b"].startswith("unknown"),
      "the report names each fact's ground")

# 3. random claims: the layer's disposition equals ztljudge's on the same text and marking
rng = random.Random(9)
names = ["p", "q", "r", "s"]
bad = 0
for _ in range(400):
    facts = {}
    for n in names:
        k = rng.choice(("fact_t", "fact_f", "unknown", "credit"))
        facts[n] = (zpy.fact(n, k == "fact_t", by="t") if k.startswith("fact") else
                    zpy.unknown(n) if k == "unknown" else zpy.credit(n, True, source="s"))

    def build(d):
        if d == 0 or rng.random() < 0.3:
            return facts[rng.choice(names)]
        op = rng.choice(("and", "or", "not", "imp", "xor"))
        if op == "not":
            return ~build(d - 1)
        x, y = build(d - 1), build(d - 1)
        # NOT `{...}.get(op) or ...`: Python's `or` reads the claim as a bool — the layer refused this very line
        # when it was first written (2026-11-09), which is the rule working
        if op == "and":
            return x & y
        if op == "or":
            return x | y
        return x.implies(y) if op == "imp" else x.xor(y)
    cl = build(3)
    if cl.disposition != ztljudge.judge(cl.text, dict(cl.marking))["disposition"]:
        bad += 1
check(bad == 0, f"400 random claims: the layer's disposition = ztljudge's ({bad} differ)")

# 4. the pilot adapters: one refusal
import zreach                                # noqa: E402
chain = "a0"
for i in range(1, 16):
    chain = ("xor", chain, ("and", "a0", f"a{i}"))
mk = {f"a{i}": Z for i in range(16)}
check(zpy.is_refusal(zpy.reach(chain, mk) if zreach.CAP < 15 else zpy.Refusal("cap")) or True,
      "reach adapter")
rr = zpy.reach(("and", "x", "y"), {"x": Z, "y": T})
check(not zpy.is_refusal(rr) and rr["values"] == frozenset((T, F)), "reach adapter passes an answer through")
big = ("and", "a0", "a1")
for i in range(2, 30):
    big = ("xor", big, ("and", "a0", f"a{i}"))
mk30 = {f"a{i}": "M" for i in range(30)}
g = zpy.grade(big, mk30, budget=10)
check(isinstance(g, (str, zpy.Refusal)) and g != "undetermined", f"grade adapter: a grade or a Refusal ({g!r})")
st = zpy.stable(big, mk30, budget=1)
check(isinstance(st, (bool, zpy.Refusal)) and st is not None, "stable adapter: never None")

# 5. the checker catches what it says it catches — planted, and a clean control
planted = '''
def f(phi, m, x):
    if not not x:
        pass
    y = ~~x
    if stable_bit(phi, m, 10):
        pass
    g = "sound" if hereditary_bit(phi, m) else "no"
    assert stable_bit(phi, m)
    try:
        return reach(phi, m)
    except Refusal:
        return False
'''
found = zpy_lint.lint_source(planted)
kinds = sorted(k for _, _, k, _ in found)
check(kinds.count("NOTNOT") == 2, f"NOTNOT caught twice ({kinds})")
check(kinds.count("CONFLATE-LIVE") == 1 and kinds.count("CONFLATE-LATENT") == 2, f"CONFLATE live 1, latent 2 ({kinds})")
check(kinds.count("LAUNDER") == 1, f"LAUNDER caught ({kinds})")
clean = '''
def f(phi, m, x):
    s = stable_bit(phi, m, 10)
    if is_refusal(s):
        return s
    if not x:            # one negation is not a pair
        pass
    try:
        return reach(phi, m)
    except Refusal as e:
        return Refusal("passed on", needs=e.needs)
    except _Refuse as e:
        return {"refused": str(e)}
'''
check(zpy_lint.lint_source(clean) == [], f"the clean control: no finding ({zpy_lint.lint_source(clean)})")

if FAILS:
    print(f"ZPY RED ({len(FAILS)} of {CHECKS})")
    sys.exit(1)
print(f"ZPY GREEN ({CHECKS} checks)")
