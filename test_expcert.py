# -*- coding: utf-8 -*-
"""
Stand: the kernel's exp brackets are covered by the Lean theorem ZExp.bracket_sound.

zfunc.exp_pt brackets e^x by reduction and squaring; zexpcert.exp_cert checks a bracket by the rule the Lean
module proves sound (ZExp.ExpCert, zero axioms, on VR's operational reals). Checks:
  1. 400 seeded rationals in [-40, 40], plus 0, +-1/4, +-10^-9, +-40: every bracket the kernel returns is
     certified — the theorem covers what the kernel outputs, not only its own series;
  2. MUTATION: a bracket that misses e^x (the kernel's hi moved to just below its lo, and lo moved past hi) is
     refused every time — the rule is not vacuous.
Run:  python3 test_expcert.py   -> EXPCERT GREEN
"""
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import zfunc                       # noqa: E402
from zexpcert import exp_cert      # noqa: E402

ok = fail = 0


def check(name, cond, why=""):
    global ok, fail
    if cond:
        ok += 1; print(f"  OK   {name}")
    else:
        fail += 1; print(f"  FAIL {name} — {why}")


rnd = random.Random(20261010)
pts = [F(0), F(1, 4), F(-1, 4), F(1, 10 ** 9), F(-1, 10 ** 9), F(40), F(-40)]
for _ in range(400):
    d = rnd.randint(1, 1000)
    pts.append(F(rnd.randint(-40 * d, 40 * d), d))
certified, bad = 0, []
refused, missed = 0, []
for x in pts:
    lo, hi = zfunc.exp_pt(x)
    good, n = exp_cert(x, lo, hi)
    if good:
        certified += 1
    else:
        bad.append((x, n))
    # a bracket that misses e^x: [lo - w, lo - w/2] lies wholly below the true value
    w = hi - lo if hi > lo else abs(lo) / 2 ** 60
    if not exp_cert(x, lo - w, lo - w / 2)[0] and not exp_cert(x, hi + w / 2, hi + w)[0]:
        refused += 1
    else:
        missed.append(x)
check(f"{len(pts)} kernel brackets of exp, x in [-40, 40]: every one certified by the Lean rule ZExp.ExpCert",
      certified == len(pts), bad[:3])
check(f"{len(pts)} brackets moved off e^x (below lo, above hi): every one refused", refused == len(pts), missed[:3])

# THE INTEGER REWRITE (2026-11-08): the same decisions as the Fractions reference, on random arguments and brackets
import math as _math
import zexpcert as _ZE
_rnd = random.Random(20261108)
_bad = _n = 0
for _ in range(600):
    _x = F(_rnd.randint(-40 * 10 ** 6, 40 * 10 ** 6), _rnd.choice([10 ** 6, 2 ** 20, 2 ** 40, 3 ** 15, 7]))
    if abs(_x) > 60:
        continue
    _v = _math.exp(float(_x))
    _w = _rnd.choice([1e-3, 1e-9, 1e-14, 0, -1e-6])
    _lo = F(_v * (1 - _w) if _w >= 0 else _v * (1 + 1e-6))
    _hi = F(_v * (1 + _w) if _w >= 0 else _v * (1 + 2e-6))
    if _rnd.random() < 0.2:
        _lo, _hi = _hi, _lo
    _bad += _ZE.exp_cert(_x, _lo, _hi) != _ZE.exp_cert_fr(_x, _lo, _hi)
    _n += 1
check(f"{_n} random arguments: zexpcert.exp_cert (integers) == exp_cert_fr (Fractions) — {_bad} disagree", _bad == 0)

print(f"\n{ok} ok, {fail} fail")
print("EXPCERT GREEN" if fail == 0 else "EXPCERT RED")
sys.exit(1 if fail else 0)
