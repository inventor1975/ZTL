# -*- coding: utf-8 -*-
"""
zdegree — ZTL degrees: the degree of a formula, exactly (2026-11-05, the curator: "да, делай").

THE QUESTION. Each atom has a degree — an interval [lo, hi] of [0, 1]: T = [1, 1], F = [0, 0], Z = [0, 1], a measured
0.3 = [3/10, 3/10]. Nobody said how the atoms are joined. The degree of a formula is the range of P(formula) over EVERY
joint distribution of its events that keeps each event's probability inside its interval: the least and the greatest.
Which occurrences are one event is the dirty rule (canon 25.10): a clean atom is one fact wherever it occurs; a dirty
atom (by default: a Z atom) is read anew at each occurrence — unless stability is assumed (`stable=True`), when its
occurrences co-refer, as in the judge's "IF STABLE".

THE METHOD. A world is a 0/1 value for every event; a joint distribution is a weight p(w) >= 0 per world, summing to 1;
event i's probability is the sum over the worlds where it is 1. The degree's ends are two linear programs:
    least / greatest  sum_{w : formula(w) = 1} p(w)   subject to   sum p = 1,  lo_i <= sum_{w_i = 1} p(w) <= hi_i.
Solved here EXACTLY, in fractions, by a two-phase simplex with Bland's rule (no float, no third-party solver). Each end
carries its proof: the distribution that attains it (checked: feasible, value equal) and the optimum of the DUAL program
(checked: equal) — so the end is attained and nothing goes past it.

WHY NOT FRECHET AT THE CORNERS (zfrechet.py's interval_out). For point inputs, and for T/F/Z inputs, a connective's
probability is linear in the joint and the corners are exact. For INTERVAL inputs they are not: XOR with A in [0, 1]
and B = 1/2 is [0, 1], while the corners say [1/2, 1/2] (the extreme sits where a + b = 1, inside the box) — measured
in the self-test. ZTL's published tables only ever feed 0, 1 or [0, 1], where the corners happen to be exact; that is
why zfrechet_tables.py stands. Beyond them, this program is the reference.

LIMITS (refused by form, never by time): at most MAX_EVENTS events after the dirty atoms are split (2^n worlds).

    python3 zdegree.py            (the self-test)
"""
from __future__ import annotations

import itertools
import random
from fractions import Fraction as Fr

from ztljudge import formalize

MAX_EVENTS = 10
ONE, ZERO = Fr(1), Fr(0)


class DegreeError(ValueError):
    pass


# ------------------------------------------------------------------ exact linear programming
def _pivot(T, r, c):
    piv = T[r][c]
    T[r] = [v / piv for v in T[r]]
    for i in range(len(T)):
        if i != r and T[i][c] != 0:
            f = T[i][c]
            T[i] = [a - f * b for a, b in zip(T[i], T[r])]


def _simplex(T, basis, ncols):
    """maximise the objective row T[-1] (stored as -c) over the tableau; Bland's rule; -> status"""
    while True:
        obj = T[-1]
        col = next((j for j in range(ncols) if obj[j] < 0), None)
        if col is None:
            return "optimal"
        best, row = None, None
        for i in range(len(T) - 1):
            if T[i][col] > 0:
                ratio = T[i][-1] / T[i][col]
                # Bland: among tied rows, the one whose basic variable has the SMALLEST index leaves (the larger one,
                # written here first, can cycle for ever — 2026-11-05 a 20-call measurement never finished)
                if best is None or ratio < best or (ratio == best and basis[i] < basis[row]):
                    best, row = ratio, i
        if row is None:
            return "unbounded"
        _pivot(T, row, col)
        basis[row] = col


def lp_max(c, rows):
    """max c.x subject to rows [(coeffs, sense, rhs)] with sense '<=', '>=' or '=', x >= 0; exact.
    -> (value, x) or raises DegreeError('infeasible')"""
    n = len(c)
    m = len(rows)
    # standard form: one slack per inequality, then make every rhs >= 0, then one artificial per row
    slack_of = {}
    ncols = n
    for i, (_a, sense, _b) in enumerate(rows):
        if sense != "=":
            slack_of[i] = ncols
            ncols += 1
    art0 = ncols
    total = ncols + m
    T, basis = [], []
    for i, (a, sense, b) in enumerate(rows):
        row = [Fr(v) for v in a] + [ZERO] * (total - n) + [Fr(b)]
        if sense == "<=":
            row[slack_of[i]] = ONE
        elif sense == ">=":
            row[slack_of[i]] = -ONE
        if row[-1] < 0:
            row = [-v for v in row]
        row[art0 + i] = ONE
        T.append(row)
        basis.append(art0 + i)
    # phase 1: minimise the sum of artificials (maximise its negative)
    obj = [ZERO] * (total + 1)
    for j in range(art0, total):
        obj[j] = ONE
    for i in range(m):
        obj = [o - t for o, t in zip(obj, T[i])]
    T.append(obj)
    _simplex(T, basis, total)
    if T[-1][-1] != 0:
        raise DegreeError("infeasible")
    # drive artificials out of the basis where possible, then drop their columns
    for i in range(m):
        if basis[i] >= art0:
            col = next((j for j in range(art0) if T[i][j] != 0), None)
            if col is not None:
                _pivot(T, i, col)
                basis[i] = col
    T = [r[:art0] + [r[-1]] for r in T[:-1]]
    # phase 2
    obj = [-Fr(v) for v in c] + [ZERO] * (art0 - n) + [ZERO]
    for i in range(m):
        if basis[i] < art0 and obj[basis[i]] != 0:
            f = obj[basis[i]]
            obj = [o - f * t for o, t in zip(obj, T[i])]
    T.append(obj)
    if _simplex(T, basis, art0) == "unbounded":
        raise DegreeError("unbounded")
    x = [ZERO] * art0
    for i in range(m):
        if basis[i] < art0:
            x[basis[i]] = T[i][-1]
    # the dual values of the inequality rows, read off the final objective row at their slack columns
    # (a '<=' slack has +1, a '>=' slack -1 in the original row; a row negated for its rhs flips both sides alike)
    duals = {i: (T[-1][col] if rows[i][1] == "<=" else -T[-1][col]) for i, col in slack_of.items()}
    lp_max.last_duals = duals
    return T[-1][-1], x[:n]


# ------------------------------------------------------------------ formulas and events
def _value(phi, w):
    if isinstance(phi, str):
        if phi in ("T", "F"):
            return 1 if phi == "T" else 0
        return w[phi]
    op = phi[0]
    if op == "not":
        return 1 - _value(phi[1], w)
    a, b = _value(phi[1], w), _value(phi[2], w)
    return {"and": a & b, "or": a | b, "imp": (1 - a) | b, "xor": a ^ b, "xnor": 1 - (a ^ b)}[op]


def _split(phi, dirty, count):
    if isinstance(phi, str):
        if phi in dirty:
            count[phi] = count.get(phi, 0) + 1
            return f"{phi}#{count[phi]}"
        return phi
    return (phi[0],) + tuple(_split(p, dirty, count) for p in phi[1:])


def _events(phi, acc):
    if isinstance(phi, str):
        if phi not in ("T", "F"):
            acc.append(phi)
    else:
        for p in phi[1:]:
            _events(p, acc)
    return acc


def as_interval(d):
    if d in ("T", "F", "Z"):
        return {"T": (ONE, ONE), "F": (ZERO, ZERO), "Z": (ZERO, ONE)}[d]
    lo, hi = (d, d) if not isinstance(d, (tuple, list)) else d
    lo, hi = Fr(lo), Fr(hi)
    if not (0 <= lo <= hi <= 1):
        raise DegreeError(f"a degree must be an interval inside [0, 1], got [{lo}, {hi}]")
    return lo, hi


def degree(formula, degrees, dirty=None, stable=False):
    """formula: ZTL text or tuple; degrees: {atom: 'T'|'F'|'Z'|number|(lo, hi)}; dirty: the atoms read anew at each
    occurrence (default: those of degree Z); stable=True makes every atom one event.
    -> {"lo", "hi", "witness_lo", "witness_hi", "events", "worlds"} with both ends proved (primal = dual)"""
    phi = formalize(formula) if isinstance(formula, str) else formula
    ivs = {a: as_interval(d) for a, d in degrees.items()}
    if dirty is None:
        dirty = {a for a, d in degrees.items() if d == "Z"}
    psi = phi if stable else _split(phi, set(dirty), {})
    events = sorted(set(_events(psi, [])))
    for e in events:
        if e.split("#")[0] not in ivs:
            raise DegreeError(f"no degree for {e.split('#')[0]!r}")
    if len(events) > MAX_EVENTS:
        raise DegreeError(f"{len(events)} events: at most {MAX_EVENTS} (2^n worlds), refused by form")
    worlds = list(itertools.product((0, 1), repeat=len(events)))
    truth = [_value(psi, dict(zip(events, w))) for w in worlds]
    rows = [([1] * len(worlds), "=", 1)]
    for k, e in enumerate(events):
        lo, hi = ivs[e.split("#")[0]]
        coeff = [w[k] for w in worlds]
        rows.append((coeff, "<=", hi))
        rows.append((coeff, ">=", lo))
    hi_val, x_hi = lp_max(truth, rows)
    duals_hi = lp_max.last_duals
    neg_lo, x_lo = lp_max([-t for t in truth], rows)
    duals_lo = lp_max.last_duals
    lo_val = -neg_lo
    # proofs: the witnesses are feasible and attain the ends; the dual optima equal the primal ones
    for x, val in ((x_hi, hi_val), (x_lo, lo_val)):
        assert all(v >= 0 for v in x) and sum(x) == 1
        for k, e in enumerate(events):
            lo, hi = ivs[e.split("#")[0]]
            m = sum(v for v, w in zip(x, worlds) if w[k])
            assert lo <= m <= hi
        assert sum(v for v, t in zip(x, truth) if t) == val
    assert _certify(truth, rows, worlds, events, ivs, hi_val, duals_hi, maximise=True)
    assert _certify(truth, rows, worlds, events, ivs, lo_val, duals_lo, maximise=False)
    return {"lo": lo_val, "hi": hi_val, "events": events, "worlds": len(worlds),
            "witness_hi": {w: v for w, v in zip(worlds, x_hi) if v}, "witness_lo": {w: v for w, v in zip(worlds, x_lo) if v}}


def degree_independent(formula, degrees, dirty=None, stable=False):
    """INDEPENDENCE, STIPULATED (a convention, never a default): every event independent of every other. Then
    P(formula) is multilinear in the events' probabilities, so over the box of their degrees its least and greatest
    values sit at CORNERS — enumerated exactly (2^k corners for the k events whose degree is not a point).
    -> {"lo", "hi", "events"}"""
    phi = formalize(formula) if isinstance(formula, str) else formula
    ivs = {a: as_interval(d) for a, d in degrees.items()}
    if dirty is None:
        dirty = {a for a, d in degrees.items() if d == "Z"}
    psi = phi if stable else _split(phi, set(dirty), {})
    events = sorted(set(_events(psi, [])))
    if len(events) > MAX_EVENTS:
        raise DegreeError(f"{len(events)} events: at most {MAX_EVENTS} (2^n worlds), refused by form")
    worlds = [w for w in itertools.product((0, 1), repeat=len(events)) if _value(psi, dict(zip(events, w)))]
    ends = [ivs[e.split("#")[0]] for e in events]
    vals = []
    for corner in itertools.product(*[sorted({lo, hi}) for lo, hi in ends]):
        vals.append(sum(_prod(corner[k] if w[k] else 1 - corner[k] for k in range(len(events))) for w in worlds))
    return {"lo": min(vals), "hi": max(vals), "events": events}


def _prod(xs):
    out = ONE
    for x in xs:
        out *= x
    return out


def _certify(truth, rows, worlds, events, ivs, value, duals, maximise):
    """WEAK DUALITY, checked: from the final tableau's duals u_i (the '<= hi' rows) and v_i (the '>= lo' rows) build
    d_i = u_i - v_i and the least y0 that keeps EVERY world's constraint y0 + d.w >= t(w) (t = truth for the greatest
    end, -truth for the least); then y0 + sum(hi_i u_i) - sum(lo_i v_i) is an upper bound on sum t.p for EVERY joint
    — and when it equals the value found, that value is the optimum, proved. Wrong duals cannot pass: the equality
    fails. Cost: one pass over the worlds."""
    t = truth if maximise else [-v for v in truth]
    u = [ZERO] * len(events)
    v = [ZERO] * len(events)
    for i, y in duals.items():
        k = (i - 1) // 2                      # rows: 0 is sum p = 1, then (<= hi, >= lo) per event
        if rows[i][1] == "<=":
            u[k] = y
        else:
            v[k] = -y
    if any(x < 0 for x in u + v):
        return False
    d = [a - b for a, b in zip(u, v)]
    y0 = max(tw - sum(dk * wk for dk, wk in zip(d, w)) for tw, w in zip(t, worlds))
    bound = y0 + sum(ivs[e.split("#")[0]][1] * uk - ivs[e.split("#")[0]][0] * vk for e, uk, vk in zip(events, u, v))
    return bound == (value if maximise else -value)


# ------------------------------------------------------------------ the self-test
def _check_one(phi):
    import zfrechet as ZF
    names = ["a", "b", "c"]
    n = 0
    for vals in itertools.product("TFZ", repeat=3):
        marking = dict(zip(names, vals))
        for stable in (False, True):
            r = degree(phi, marking, stable=stable)
            want = ZF.degree_01(phi, marking, separate=not stable)
            assert (r["lo"], r["hi"]) == want, (phi, marking, stable, r["lo"], r["hi"], want)
            n += 1
    return n


def _selftest():
    print("ZDEGREE — the degree of a formula, exactly")
    rng = random.Random(51)
    # 1. on T/F/Z degrees the program agrees with the enumeration of zfrechet.degree_01, both read modes
    import os
    import zfrechet as ZF
    names = ["a", "b", "c"]
    phis = [ZF.rand_formula(rng, names, 3) for _ in range(120)]
    # ON EVERY CORE (the curator, 2026-11-05: "этот тест на всех ядрах запускай"); one process inside run_all
    # (ZTL_SUITE), which already fills the machine. MEASURED: one call 0.002 s median, 0.071 s at 8 events.
    procs = 1 if os.environ.get("ZTL_SUITE") else min(24, os.cpu_count() or 1)
    if procs > 1:
        from multiprocessing import Pool
        with Pool(procs) as pool:
            counts = pool.map(_check_one, phis, chunksize=4)
    else:
        counts = [_check_one(phi) for phi in phis]
    print(f"  1. T/F/Z degrees: {sum(counts)} formula-marking-mode cases equal the enumeration (both read modes;"
          f" {procs} process(es))")
    # 2. point degrees, one connective: the Fréchet formula exactly
    a, b = Fr(3, 10), Fr(7, 10)
    for txt, want in (("x & y", (0, Fr(3, 10))), ("x | y", (Fr(7, 10), 1)), ("x -> y", (Fr(7, 10), 1)),
                      ("x ^ y", (Fr(2, 5), 1)), ("x = y", (0, Fr(3, 5))), ("~(x & y)", (Fr(7, 10), 1))):
        r = degree(txt, {"x": a, "y": b})
        assert (r["lo"], r["hi"]) == tuple(Fr(v) for v in want), (txt, r["lo"], r["hi"])
    print("  2. point degrees 3/10, 7/10: and, or, imp, xor, xnor, nand = the Fréchet intervals")
    # 3. one fact is one event: classical laws hold on a clean atom of any degree
    for d in (Fr(3, 10), (Fr(1, 5), Fr(2, 5))):
        assert (degree("x & ~x", {"x": d})["lo"], degree("x & ~x", {"x": d})["hi"]) == (0, 0)
        assert (degree("x | ~x", {"x": d})["lo"], degree("x | ~x", {"x": d})["hi"]) == (1, 1)
        r = degree("(x & y) | (x & ~y)", {"x": d, "y": Fr(1, 2)})
        assert (r["lo"], r["hi"]) == as_interval(d)
    r = degree("x & ~x", {"x": Fr(3, 10)}, dirty={"x"})
    assert (r["lo"], r["hi"]) == (0, Fr(3, 10))
    print("  3. clean: x & ~x = [0,0], x | ~x = [1,1], (x&y)|(x&~y) = x's own degree; dirty x & ~x = [0, 3/10]")
    # 4. interval inputs: where Fréchet at the corners is wrong
    r = degree("x ^ y", {"x": (0, 1), "y": Fr(1, 2)}, dirty=set())
    corners = ZF.interval_out(lambda p, q: p ^ q, (ZERO, ONE), (Fr(1, 2), Fr(1, 2)))
    assert (r["lo"], r["hi"]) == (0, 1) and corners == (Fr(1, 2), Fr(1, 2))
    print(f"  4. x ^ y with x in [0,1], y = 1/2: exactly [0, 1]; the corners said [{corners[0]}, {corners[1]}]")
    # 5. independence, stipulated, lands inside; widening a degree widens the result
    for _ in range(60):
        phi = ZF.rand_formula(rng, ["a", "b"], 3)
        pa, pb = Fr(rng.randint(0, 10), 10), Fr(rng.randint(0, 10), 10)
        r = degree(phi, {"a": pa, "b": pb})
        ind = sum((pa if w[0] else 1 - pa) * (pb if w[1] else 1 - pb)
                  for w in itertools.product((0, 1), repeat=2) if _value(phi, {"a": w[0], "b": w[1]}))
        assert r["lo"] <= ind <= r["hi"]
        wide = degree(phi, {"a": (max(ZERO, pa - Fr(1, 10)), min(ONE, pa + Fr(1, 10))), "b": pb})
        assert wide["lo"] <= r["lo"] and r["hi"] <= wide["hi"]
    for _ in range(40):
        phi = ZF.rand_formula(rng, ["a", "b", "c"], 3)
        dg = {k: (Fr(rng.randint(0, 5), 10), Fr(rng.randint(5, 10), 10)) for k in ("a", "b", "c")}
        free, ind = degree(phi, dg), degree_independent(phi, dg)
        assert free["lo"] <= ind["lo"] <= ind["hi"] <= free["hi"], (phi, dg)
    print("  5. independence lands inside every interval; widening a degree never narrows the result (60 formulas)")
    # 6. refusals by form
    for bad in ({"x": Fr(3, 2)}, {"x": (Fr(1, 2), Fr(1, 4))}):
        try:
            degree("x", bad)
            raise AssertionError("not refused")
        except DegreeError:
            pass
    try:
        degree(" & ".join(f"v{i}" for i in range(MAX_EVENTS + 1)), {f"v{i}": "Z" for i in range(MAX_EVENTS + 1)})
        raise AssertionError("not refused")
    except DegreeError:
        pass
    print(f"  6. a degree outside [0, 1], an empty interval, more than {MAX_EVENTS} events: refused by form")
    # 7. a wrong end cannot pass its certificate (both sides: the true end passes, a nudged one fails)
    phi = formalize("(x & y) | ~z")
    ivs = {"x": (Fr(1, 5), Fr(1, 2)), "y": (Fr(1, 3), Fr(1, 3)), "z": (Fr(1, 2), Fr(3, 5))}
    r = degree(phi, ivs)
    events = sorted(set(_events(phi, [])))
    worlds = list(itertools.product((0, 1), repeat=len(events)))
    truth = [_value(phi, dict(zip(events, w))) for w in worlds]
    rows = [([1] * len(worlds), "=", 1)]
    for k, e in enumerate(events):
        coeff = [w[k] for w in worlds]
        rows += [(coeff, "<=", ivs[e][1]), (coeff, ">=", ivs[e][0])]
    val, _x = lp_max(truth, rows)
    duals = lp_max.last_duals
    assert val == r["hi"] and _certify(truth, rows, worlds, events, ivs, val, duals, True)
    assert not _certify(truth, rows, worlds, events, ivs, val - Fr(1, 100), duals, True)
    assert not _certify(truth, rows, worlds, events, ivs, val + Fr(1, 100), duals, True)
    print(f"  7. the certificate passes the true greatest end {val} and refuses it nudged by 1/100 either way")
    print("ZDEGREE GREEN — every end proved twice: a distribution that attains it, a dual that bounds it")


if __name__ == "__main__":
    _selftest()
