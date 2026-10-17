# -*- coding: utf-8 -*-
"""
Red-team stand for the Taylor-leaf line (2026-10-17: zcertify.taylor_coeffs, ztaylorcert.check, zintegral's
{"taylor": n} leaf, lean/ZJetRead CRead + ZJetClose.taylorN_kernel). The report: the commit that registered this stand.

Each FINDING block is RED while the finding stands; each CONTROL block is GREEN (what was attacked and held).
Written by a red-team agent 2026-10-17 (RED 10/15 on 6187278); the five findings fixed the same day, the stand
registered in run_all.py (GREEN 15/15).

Run:  python3 test_redteam_taylor.py   -> REDTEAM TAYLOR GREEN | REDTEAM TAYLOR RED (n findings)
"""
import os
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import zcertify as ZC              # noqa: E402
import zintegral as ZI             # noqa: E402
import ztaylorcert as T            # noqa: E402
from znumjudge import _parse_arith, parse_quantities   # noqa: E402

RED, GREEN = [], []


def finding(name, holds_ok, msg):
    """holds_ok: True when the claim survives (the finding is gone)."""
    (GREEN if holds_ok else RED).append(name)
    print(("  ok    " if holds_ok else "  RED   ") + f"[{name}] {msg}")


def control(name, cond, msg):
    (GREEN if cond else RED).append(name)
    print(("  ok    " if cond else "  RED   ") + f"[{name}] {msg}")


def fs(v):
    return f"{v.numerator}/{v.denominator}"


def setup(t, boxes):
    qs = parse_quantities(", ".join(f"{n}=[{fs(a)},{fs(b)}] credit" for n, (a, b) in boxes.items()))[0]
    return _parse_arith(t, qs), qs


def naive(node, box):
    """The tightest interval Lean's VRead can give for a node of + - * const var: VRead.add/sub/mul only WIDEN the
    corner/endpoint arithmetic (`qle l (...)`, `Corners`), VRead.var only widens the box. So naive(arg)[0] is an UPPER
    bound for the lower end of EVERY VRead of arg (exact rationals)."""
    if isinstance(node, (int, F)):
        return F(node), F(node)
    if isinstance(node, str):
        return box[node]
    op, a, b = node
    A, B = naive(a, box), naive(b, box)
    if op == "add":
        return A[0] + B[0], A[1] + B[1]
    if op == "sub":
        return A[0] - B[1], A[1] - B[0]
    if op == "mul":
        ps = [x * y for x in A for y in B]
        return min(ps), max(ps)
    raise ValueError(op)


def raises(fn):
    try:
        fn()
        return None
    except Exception as ex:                     # noqa: BLE001 — the finding IS the escaping exception
        return f"{type(ex).__name__}: {ex}"


print("F1. value readings from znum's EXACT LINEAR fragment are trusted as Lean VReads (ztaylorcert._value_covered)")
# CRead.sqrt needs VRead B (.sqrt u) l0 h0 with 0 < l0; VRead.sqrt needs VRead B u lu hu with 0 <= lu. For
# u = 1 + 2x - x over x in [0, 2] every VRead of u has lu <= naive lower = 1 + 0 - 2 = -1 < 0: NO VRead of sqrt(u)
# exists, hence no CRead of any series of sqrt(u) over this piece. The kernel reads u exactly ([1, 3], _ev_linear).
e, qs = setup("sqrt(1 + 2*x - x)", {"x": (F(0), F(2))})
piece = {"x": (F(0), F(2))}
tr = {}
cs = ZC.taylor_coeffs(e, "x", qs, piece, 4, trace=tr)
lo_arg = naive(e[1], piece)[0]
good, why, fault = T.check(e, "x", qs, piece, 4, cs, tr)
print(f"        kernel's own series of the argument, c0 = {tuple(map(str, tr[e[1]][0]))}; sqrt's c0 = "
      f"[{float(cs[0][0]):.6g}, {float(cs[0][1]):.6g}]; every VRead of the argument has lu <= {lo_arg}")
finding("F1-sqrt-check", not good or lo_arg >= 0,
        f"ztaylorcert.check -> {(good, why, fault)} although CRead.sqrt is impossible over [0, 2]")
ZI.TAYLOR_PREMISE.clear()
ZI.TAYLOR_FAULT[0] = 0
r = ZI.check(e, "x", 0, 2, qs, {"points": ["0", "2"], "leaves": [{"taylor": 4}]})
finding("F1-sqrt-run", (not r[0]) or bool(ZI.TAYLOR_PREMISE),
        f"zintegral.check accepted={r[0]} with TAYLOR_PREMISE={ZI.TAYLOR_PREMISE}: counted as Lean-covered")

# the same through a node WITHOUT x (CRead.free needs VRead B e l h of the whole node)
e2, qs2 = setup("x*sqrt(1 + 2*p - p)", {"x": (F(0), F(1)), "p": (F(0), F(2))})
box2 = {"x": (F(0), F(1)), "p": (F(0), F(2))}
tr2 = {}
cs2 = ZC.taylor_coeffs(e2, "x", qs2, {"x": (F(0), F(1))}, 4, trace=tr2)
good2, why2, _ = T.check(e2, "x", qs2, {"x": (F(0), F(1))}, 4, cs2, tr2)
finding("F1-free-check", not good2 or naive(e2[2][1], box2)[0] >= 0,
        f"free node sqrt(1 + 2p - p), p in [0, 2]: check -> {(good2, why2)}; every VRead of its argument has "
        f"lu <= {naive(e2[2][1], box2)[0]}")

print("F2. a 'sum' node: the checker's sum branch is unreachable, a root sum raises")
fsum = ("sum", ["x", ("exp", "x")])
_, qx = setup("x", {"x": (F(0), F(1))})
err = raises(lambda: ZI.check(fsum, "x", 0, 1, qx, {"points": ["0", "1"], "leaves": [{"taylor": 4}]}))
finding("F2-root-sum", err is None, f"zintegral.check(sum(x, exp(x)), taylor 4) -> {err or 'a verdict'}")
trs = {}
css = ZC.taylor_coeffs(fsum, "x", qx, {"x": (F(1, 4), F(3, 8))}, 4, trace=trs)
err = raises(lambda: T.check(fsum, "x", qx, {"x": (F(1, 4), F(3, 8))}, 4, css, trs))
finding("F2-check-sum", err is None, f"ztaylorcert.check on a kernel series of sum(x, exp(x)) -> {err or 'a verdict'}")

print("F3. exceptions escape the Taylor leaf (and search) where the interval leaf refuses")
e3, q3 = setup("exp(tan(x))", {"x": (F(0), F(2))})
a3, b3 = F(3, 2), F(25, 16)
ri = ZI.check(e3, "x", a3, b3, q3, {"points": [fs(a3), fs(b3)], "leaves": ["interval"]})
err = raises(lambda: ZI.check(e3, "x", a3, b3, q3, {"points": [fs(a3), fs(b3)], "leaves": [{"taylor": 2}]}))
finding("F3-tan-leaf", err is None, f"exp(tan x) on [3/2, 25/16]: interval leaf -> {ri}; taylor leaf -> {err or 'a verdict'}")
err = raises(lambda: ZI.search(e3, "x", F(1), b3, q3, F(1, 1000)))
finding("F3-tan-search", err is None, f"search(exp(tan x), [1, 25/16]) -> {err or 'a result'}")
e4 = ("min", "x", ("sub", 1, "x"))
err = raises(lambda: ZI.check(e4, "x", 0, 1, qx, {"points": ["0", "1"], "leaves": [{"taylor": 2}]}))
finding("F3-min-leaf", err is None, f"min(x, 1 - x), taylor leaf (symbolic fallback) -> {err or 'a verdict'}")

print("F4. check2's outer Taylor leaf: symbolic derivatives, no ztaylorcert, not counted in TAYLOR_PREMISE")
e5, q5 = setup("exp(x*y)", {"x": (F(0), F(1)), "y": (F(0), F(1))})
ZI.TAYLOR_PREMISE.clear()
ins = [{"points": ["0", "1"], "leaves": ["interval"]}] * 3
r5 = ZI.check2(e5, "x", 0, 1, "y", 0, 1, q5, {"points": ["0", "1"], "leaves": [{"taylor": 4, "inner": ins}]})
finding("F4-check2", (not r5[0]) or bool(ZI.TAYLOR_PREMISE),
        f"check2 accepted={r5[0]} (enclosure {[float(v) for v in r5[1]] if r5[0] else r5[1]}), "
        f"TAYLOR_PREMISE={ZI.TAYLOR_PREMISE}")

print("F5. check() never reads CRead.var (nor free nodes' zeros, nor any k = 0 Hull): a wrong x-series passes")
# MUTATION: the kernel's series of exp(sin(2x))*(2x), relabelled onto exp(sin(x))*x — every recurrence holds, but x's
# own series is [2X, 2, 0, ...]: CRead.var needs c1 ⊇ [1, 1], so NO CRead of this trace exists. check says True.
e7, q7 = setup("exp(sin(x))*x", {"x": (F(0), F(1))})
pc7 = {"x": (F(1, 4), F(3, 8))}
e7b = ("mul", ("exp", ("sin", ("mul", 2, "x"))), ("mul", 2, "x"))
t7 = {}
ZC.taylor_coeffs(e7b, "x", q7, pc7, 4, trace=t7)
ren = {e7b: e7, e7b[1]: e7[1], e7b[1][1]: e7[1][1], ("cos", ("mul", 2, "x")): ("cos", "x"), ("mul", 2, "x"): "x"}
t7r = {ren[k]: v for k, v in t7.items() if k in ren}
g7 = T.check(e7, "x", q7, pc7, 4, t7r[e7], t7r)
finding("F5-var-unchecked", not g7[0], f"x's series {[str(c[0]) + '..' + str(c[1]) for c in t7r['x'][:3]]} -> check {g7}")

print("CONTROLS (attacked, held)")
try:
    import mpmath as mp
    mp.mp.dps = 50
    for t, a, b, fn in (("sqrt(1 + 2*x - x)", 0, 2, lambda x: mp.sqrt(1 + x)),
                        ("exp(2*x - x)", 0, 1, lambda x: mp.exp(x)),
                        ("tan(x)*tan(x)", F(11, 8), F(11, 8) + F(1, 1024), lambda x: mp.tan(x) ** 2),
                        ("pow(sin(x) + 2, 7)", F(-1, 3), F(-1, 3) + F(1, 2 ** 20), lambda x: (mp.sin(x) + 2) ** 7)):
        ee, qq = setup(t, {"x": (F(-2), F(2))})
        g = ZI.check(ee, "x", F(a), F(b), qq, {"points": [fs(F(a)), fs(F(b))], "leaves": [{"taylor": 12}]})
        I = mp.quad(fn, [mp.mpf(F(a).numerator) / F(a).denominator, mp.mpf(F(b).numerator) / F(b).denominator])
        ins_ = g[0] and mp.mpf(g[1][0].numerator) / g[1][0].denominator <= I <= mp.mpf(g[1][1].numerator) / g[1][1].denominator
        control("C-sound-" + t, ins_, f"{t} on [{a}, {b}], taylor 12: mpmath value inside the accepted enclosure")
except ImportError:
    print("  (mpmath not installed: soundness controls skipped)")
tr6 = {}
e6, q6 = setup("pow(x + 2, 5)*exp(sin(x))/(1 + x*x)", {"x": (F(0), F(1))})
cs6 = ZC.taylor_coeffs(e6, "x", q6, {"x": (F(1, 4), F(3, 8))}, 8, trace=tr6)
control("C-mirror", T.check(e6, "x", q6, {"x": (F(1, 4), F(3, 8))}, 8, cs6, tr6)[0],
        "a covered integrand's series passes the mirror (sanity: the checker is not trivially red)")

print()
reds = [n for n in RED]
if reds:
    print(f"REDTEAM TAYLOR RED ({len(reds)} red: {', '.join(reds)}; {len(GREEN)} ok)")
    sys.exit(1)
print(f"REDTEAM TAYLOR GREEN ({len(GREEN)} checks)")
