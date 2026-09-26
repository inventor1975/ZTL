# -*- coding: utf-8 -*-
"""
redteam_numeric_load — targeted load probes and crash reproductions for the
numeric judge (red team, 2026-09-26). Not a stand: it prints timings (median
of 3 compare() calls) and what each refusal-by-exception looks like.

Run: python3 inventory/probes/redteam_numeric_load.py
"""
import os, sys, time, statistics
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
import znum
from fractions import Fraction as Q


def T(label, kind, e1, e2, qs, reps=3):
    ts = []
    for _ in range(reps):
        t = time.perf_counter()
        try:
            r = znum.compare(kind, e1, e2, qs)[0]
        except BaseException as ex:          # noqa: BLE001 — the refusal is the finding
            r = "EXC:" + type(ex).__name__
        ts.append((time.perf_counter() - t) * 1000)
    print(f"{statistics.median(ts):9.1f} ms  {r:5} {label}")


def prod(fs):
    e = fs[0]
    for f in fs[1:]:
        e = ("mul", e, f)
    return e


print("-- load")
X = 'x'

C=znum.qty(-10**6,10**6)
# degree 8, product of (x - r_i) with ugly rationals
for den in (7, 997, 10**6+3, 10**12+39):
    rs=[Q(k*37+1, den) for k in range(8)]
    T(f"deg-8 product, roots k/{den}", 'le', prod([('sub',X,r) for r in rs]), 1, {'x':C})
for c in (10**3, 10**12, 10**30):
    T(f"deg-8 sum of big-coefficient monomials c={c:.0e}", 'le',
      ('add', prod([X]*8), ('mul', Q(c)+Q(1,3), prod([X]*7))), 0, {'x':C})
# int refine (2): x*x == K*y, residue loop
for K in (9973, 9999, 10000):
    T(f"int (2) residue loop x*x + x == {K}*y", 'eq', ('add',('mul',X,X),X), ('mul',K,'y'),
      {'x':znum.qty(-10**9,10**9,discrete='int'),'y':znum.qty(-10**9,10**9,discrete='int')})
# int refine (3): bilinear, N near the 10^10 ceiling, prime
for N in (9999999967, 10**10):
    T(f"int (3) bilinear x*y == {N}", 'eq', ('mul',X,'y'), N,
      {'x':znum.qty(2,10**12,discrete='int'),'y':znum.qty(2,10**12,discrete='int')})
# multilinear, many keys through samples (the API has no depth cap)
s={'s':znum.qty(-3,5,sample=True)}
T("multilinear 10 sample keys", 'le', prod(['s']*10), 10**9, s)
T("RecursionError quartic (see report)", 'le',
  ('add',('add',('mul',Q(1,4),prod([X]*4)),('mul',-Q(1,8*10**12),prod([X]*3))),('mul',Q(1,8*10**12)**2,prod([X]*2))),
  1, {'x':znum.qty(0,Q(2,8*10**12))})

print("-- refusals by exception on admissible input (not lies)")


def R(label, f):
    try:
        out = f()
        print(f"  ok      {label}: {out[0] if isinstance(out, tuple) else 'built'}")
    except BaseException as ex:              # noqa: BLE001
        print(f"  {type(ex).__name__:15s} {label}: {str(ex)[:70]}")


R("sqrt(z), z in [4, inf)", lambda: znum.compare("le", "x", ("sqrt", "z"),
  {"x": znum.qty(0, 1), "z": znum.qty(4, znum.INF)}))
R("int quantity pinned at +inf", lambda: znum.qty(znum.INF, znum.INF, discrete="int"))
R("(1/x)*x <= 5, x in metres", lambda: znum.compare("le", ("mul", ("div", 1, "x"), "x"), 5,
  {"x": znum.qty(1, 2, unit="m")}))
