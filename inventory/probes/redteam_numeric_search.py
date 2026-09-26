# -*- coding: utf-8 -*-
"""
redteam_numeric_search — falsification search against the numeric judge.

Question: does `znum.compare` ever return a WRONG forced verdict? T means "holds
under EVERY admissible reading", F "fails under every one". Z and E are never
wrong, so only T and F are tested: for a T the search looks for ONE admissible
reading where the claim is false, for an F one where it is true. Any such
reading is a proven lie.

The gold here is written from the SEMANTICS, not from znum: nothing below
imports znum's evaluators. Readings of a quantity are its lattice ∩ [lo, hi]
(continuous = the rationals); a name is one number across the whole claim,
except a `sample`, where every occurrence is its own reading. Arithmetic is
exact (fractions.Fraction); a square root that is not a rational square is
held as a tight rational enclosure, and a comparison the enclosure cannot
decide is left UNDECIDED — never counted as a counterexample.

How a forced verdict is checked, strongest first (each claim gets one label):
  exact-enum    every reading of a finite box enumerated;
  exact-lines   the claim is a polynomial of degree <= 2 in one "line" name
                once the others are fixed, and every fixing of the others is
                enumerated: along each line the extremes and the lattice /
                rational roots are computed exactly, so the whole box is
                decided without listing the line;
  searched      a finite candidate set: bounds and their lattice neighbours,
                lattice points near 0, rational midpoints, random lattice
                points, critical points of the quadratic faces, and roots and
                critical points along coordinate lines (Sturm-free bracketing
                refined to 2^-70 and snapped to the lattice / to small
                denominators). "No lie" there means "none in this set".

Run (the numbers in REDTEAM-NUMERIC-2026-09.md come from exactly this):
    python3 inventory/probes/redteam_numeric_search.py --seed 20260926 \
        --workers 4 --out /tmp/redteam.json
    python3 inventory/probes/redteam_numeric_search.py --only sum --n 2000
Everything is seeded: a chunk's generator is random.Random(f"{frag}:{seed}:{k}").
Timing is the only non-deterministic output.
"""
import argparse
import itertools
import json
import math
import os
import random
import sys
import time
from fractions import Fraction as Q

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, ROOT)

INF = math.inf
SLOW_MS = 50.0
ENUM_MAX = 1500          # readings enumerated outright
LINE_FIX_MAX = 400       # fixings enumerated for exact-lines


# ===================================================================== gold
class Undef(Exception):
    """The claim has no value at this reading (x/0, sqrt of a negative)."""


class Undecided(Exception):
    """An irrational enclosure straddles the point that would decide it."""


SQ = 10 ** 40


def _sqrt_enc(x):
    """Rational enclosure of sqrt(x), x >= 0 exact; a point when exact."""
    if x < 0:
        raise Undef("sqrt<0")
    if x == 0:
        return Q(0), Q(0)
    p, q = x.numerator, x.denominator
    rp, rq = math.isqrt(p), math.isqrt(q)
    if rp * rp == p and rq * rq == q:
        v = Q(rp, rq)
        return v, v
    n = p * SQ * SQ
    return Q(math.isqrt(n // q), SQ), Q(math.isqrt(-(-n // q)) + 1, SQ)


def _mul(a, b):
    ps = [x * y for x in a for y in b]
    return min(ps), max(ps)


def gev(e, env):
    """Exact value (lo == hi) or a tight enclosure of an expression at a
    reading. `env` maps every variable to a Fraction."""
    if isinstance(e, Q):
        return e, e
    if isinstance(e, str):
        v = env[e]
        return v, v
    op = e[0]
    if op == "sum":
        lo = hi = Q(0)
        for a in e[1]:
            l, h = gev(a, env)
            lo, hi = lo + l, hi + h
        return lo, hi
    if op == "sqrt":
        l, h = gev(e[1], env)
        if l == h:
            return _sqrt_enc(l)
        if h < 0:
            raise Undef("sqrt<0")
        if l < 0:
            raise Undecided()
        return _sqrt_enc(l)[0], _sqrt_enc(h)[1]
    a, b = gev(e[1], env), gev(e[2], env)
    if op == "add":
        return a[0] + b[0], a[1] + b[1]
    if op == "sub":
        return a[0] - b[1], a[1] - b[0]
    if op == "mul":
        return _mul(a, b)
    if op == "div":
        if b[0] == b[1] == 0:
            raise Undef("div0")
        if b[0] <= 0 <= b[1]:
            raise Undecided()
        return _mul(a, (1 / b[1], 1 / b[0]))
    raise ValueError(op)


def gtruth(kind, e1, e2, env):
    """True / False / 'undef' / None (undecided) at one reading."""
    try:
        a, b = gev(e1, env), gev(e2, env)
    except Undef:
        return "undef"
    except Undecided:
        return None
    lo, hi = a[0] - b[1], a[1] - b[0]
    if kind == "le":
        return True if hi <= 0 else (False if lo > 0 else None)
    if kind == "lt":
        return True if hi < 0 else (False if lo >= 0 else None)
    if lo == hi:
        return lo == 0
    return False if (lo > 0 or hi < 0) else None


def step_of(discrete):
    if discrete is None:
        return None
    if discrete == "int":
        return Q(1)
    if discrete[0] == "decimal":
        return Q(1, 10 ** discrete[1])
    return Q(1, discrete[1])


def dom(spec):
    """(first, last, step) of the reading set, or None when it is empty.
    Ends may be ±INF. Continuous readings are the RATIONALS, so a
    continuous quantity pinned at an infinity has no reading at all."""
    lo, hi, st = spec["lo"], spec["hi"], step_of(spec["discrete"])
    if lo > hi:
        return None
    if st is None:
        if lo == hi and isinstance(lo, float):
            return None
        return lo, hi, None
    first = lo if lo == -INF else (Q(math.ceil(lo / st)) * st if not isinstance(lo, float) else None)
    last = hi if hi == INF else (Q(math.floor(hi / st)) * st if not isinstance(hi, float) else None)
    if first is None or last is None:      # a lattice pinned at an infinity
        return None
    if first > last:
        return None
    return first, last, st


def dom_size(d):
    first, last, st = d
    if first == last:
        return 1
    if st is None or isinstance(first, float) or isinstance(last, float):
        return INF
    return int((last - first) / st) + 1


def dom_points(d):
    first, last, st = d
    if first == last:
        return [first]
    n = int((last - first) / st)
    return [first + k * st for k in range(n + 1)]


def in_dom(v, d):
    first, last, st = d
    if isinstance(v, float) or v < first or v > last:
        return False
    return st is None or (v / st).denominator == 1


def expand(e1, e2, specs):
    """Rename every occurrence of a sample name to its own variable."""
    count = {}
    varspec = {}

    def walk(e):
        if isinstance(e, str):
            s = specs[e]
            if s.get("sample"):
                count[e] = count.get(e, 0) + 1
                v = f"{e}#{count[e]}"
            else:
                v = e
            varspec[v] = s
            return v
        if isinstance(e, Q):
            return e
        if e[0] == "sum":
            return ("sum", [walk(a) for a in e[1]])
        if e[0] == "sqrt":
            return ("sqrt", walk(e[1]))
        return (e[0], walk(e[1]), walk(e[2]))
    return walk(e1), walk(e2), varspec


# ------------------------------------------------------------ polynomials
class NotPoly(Exception):
    pass


def mpoly(e):
    """{monomial: coef}, monomial = tuple(sorted((var, power))). Division
    only by a nonzero constant, sqrt only of an exact rational square."""
    if isinstance(e, Q):
        return {(): e} if e else {}
    if isinstance(e, str):
        return {((e, 1),): Q(1)}
    op = e[0]
    if op == "sum":
        out = {}
        for a in e[1]:
            for m, c in mpoly(a).items():
                out[m] = out.get(m, 0) + c
        return {m: c for m, c in out.items() if c}
    if op == "sqrt":
        a = mpoly(e[1])
        if set(a) - {()}:
            raise NotPoly()
        c = a.get((), Q(0))
        l, h = _sqrt_enc(c) if c >= 0 else (None, None)
        if l is None or l != h:
            raise NotPoly()
        return {(): l} if l else {}
    a, b = mpoly(e[1]), mpoly(e[2])
    if op in ("add", "sub"):
        out = dict(a)
        for m, c in b.items():
            out[m] = out.get(m, 0) + (c if op == "add" else -c)
        return {m: c for m, c in out.items() if c}
    if op == "mul":
        out = {}
        for m1, c1 in a.items():
            for m2, c2 in b.items():
                pw = dict(m1)
                for v, k in m2:
                    pw[v] = pw.get(v, 0) + k
                m = tuple(sorted(pw.items()))
                out[m] = out.get(m, 0) + c1 * c2
        return {m: c for m, c in out.items() if c}
    if op == "div":
        if set(b) - {()} or not b:
            raise NotPoly()
        k = b[()]
        return {m: c / k for m, c in a.items()}
    raise NotPoly()


def restrict(P, env, v):
    """Univariate coefficients (low -> high) of P in v, others from env."""
    out = {}
    for m, c in P.items():
        k = 0
        for u, p in m:
            if u == v:
                k = p
            else:
                c = c * env[u] ** p
        out[k] = out.get(k, 0) + c
    deg = max(out) if out else 0
    return [out.get(i, Q(0)) for i in range(deg + 1)]


def peval(a, x):
    r = Q(0)
    for c in reversed(a):
        r = r * x + c
    return r


def trim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def rat_sqrt(x):
    if x < 0:
        return None
    l, h = _sqrt_enc(x)
    return l if l == h else None


# goals: what a counterexample needs of d = e1 - e2 at a reading
def goal_of(kind, verdict):
    """For a T we want the claim FALSE, for an F we want it TRUE."""
    want_true = verdict == "F"
    return {("le", True): "d<=0", ("le", False): "d>0",
            ("lt", True): "d<0", ("lt", False): "d>=0",
            ("eq", True): "d==0", ("eq", False): "d!=0"}[(kind, want_true)]


def meets(goal, d):
    return {"d<=0": d <= 0, "d>0": d > 0, "d<0": d < 0, "d>=0": d >= 0,
            "d==0": d == 0, "d!=0": d != 0}[goal]


def line_exact(a, d, goal):
    """EXACT answer along one line: coefficients a (degree <= 2) of d(t),
    t ranging over the domain d. Returns a witness t or None (none exists).
    Raises NotPoly if the line is not decidable here (degree > 2, or an
    infinite lattice end the formulas below do not cover)."""
    a = trim(a)
    if len(a) > 3:
        raise NotPoly()
    first, last, st = d
    fin_lo, fin_hi = not isinstance(first, float), not isinstance(last, float)
    if st is not None:
        if not (fin_lo and fin_hi):
            raise NotPoly()
        # t = first + st*k, k in 0..n: re-express in k
        n = int((last - first) / st)
        c0 = a + [Q(0)] * (3 - len(a))
        A = c0[2] * st * st
        B = (2 * c0[2] * first + c0[1]) * st
        C = c0[2] * first * first + c0[1] * first + c0[0]
        f = lambda k: A * k * k + B * k + C
        tv = lambda k: first + st * k
        if goal in ("d==0",):
            if A == 0 and B == 0:
                return tv(0) if C == 0 else None
            if A == 0:
                k = -C / B
                return tv(k) if k.denominator == 1 and 0 <= k <= n else None
            D = B * B - 4 * A * C
            s = rat_sqrt(D)
            if s is None:
                return None
            for k in ((-B + s) / (2 * A), (-B - s) / (2 * A)):
                if k.denominator == 1 and 0 <= k <= n:
                    return tv(k)
            return None
        if goal == "d!=0":
            for k in (0, n, min(n, 1), min(n, 2)):
                if f(k) != 0:
                    return tv(k)
            return None
        cand = {0, n}
        if A != 0:
            v = -B / (2 * A)
            for k in (math.floor(v), math.ceil(v)):
                if 0 <= k <= n:
                    cand.add(k)
        for k in cand:
            if meets(goal, f(k)):
                return tv(k)
        return None
    # continuous: the rationals in [first, last]
    c0 = a + [Q(0)] * (3 - len(a))
    A, B, C = c0[2], c0[1], c0[0]
    f = lambda t: A * t * t + B * t + C
    if first == last:
        return first if meets(goal, f(first)) else None
    def inside(t):
        return (not fin_lo or t >= first) and (not fin_hi or t <= last)
    if goal == "d==0":
        if A == 0 and B == 0:
            return (first if fin_lo else (last if fin_hi else Q(0))) if C == 0 else None
        if A == 0:
            t = -C / B
            return t if inside(t) else None
        s = rat_sqrt(B * B - 4 * A * C)
        if s is None:
            return None
        for t in ((-B + s) / (2 * A), (-B - s) / (2 * A)):
            if inside(t):
                return t
        return None
    pts = []
    if fin_lo:
        pts.append(first)
    if fin_hi:
        pts.append(last)
    if A != 0:
        v = -B / (2 * A)
        if inside(v):
            pts.append(v)
    # an infinite end: walk out along it
    for sgn, fin in ((-1, fin_lo), (1, fin_hi)):
        if not fin:
            base = last if sgn < 0 and fin_hi else (first if sgn > 0 and fin_lo else Q(0))
            for e in (1, 3, 6, 12, 24, 48):
                pts.append(base + sgn * Q(10) ** e)
    if not pts:
        pts = [Q(0)]
    for t in pts:
        if meets(goal, f(t)):
            return t
    # complete: a quadratic's extremes over an interval sit at the ends and
    # the vertex, and a strict inequality that holds anywhere holds there;
    # along an infinite end the leading term decides by t = 10^48
    return None


def _brackets(a, lo, hi, grid=48):
    """Sign-change brackets of a polynomial on [lo, hi] (finite), refined."""
    xs = [lo + (hi - lo) * Q(i, grid) for i in range(grid + 1)]
    vs = [peval(a, x) for x in xs]
    out = []
    for i in range(grid):
        if vs[i] == 0:
            out.append((xs[i], xs[i]))
        elif (vs[i] > 0) != (vs[i + 1] > 0) and vs[i + 1] != 0:
            l, h, fl = xs[i], xs[i + 1], vs[i]
            for _ in range(70):
                m = (l + h) / 2
                fm = peval(a, m)
                if fm == 0:
                    l = h = m
                    break
                if (fm > 0) == (fl > 0):
                    l, fl = m, fm
                else:
                    h = m
            out.append((l, h))
    if vs[-1] == 0:
        out.append((xs[-1], xs[-1]))
    return out


def line_candidates(a, d):
    """Candidate t along a line for a polynomial of any degree: ends,
    lattice-snapped roots and critical points (bracketed), small-denominator
    rationals near them."""
    first, last, st = d
    a = trim(a)
    lo = first if not isinstance(first, float) else None
    hi = last if not isinstance(last, float) else None
    cb = 1 + max((abs(c / a[-1]) for c in a[:-1]), default=Q(0)) if a[-1] != 0 and len(a) > 1 else Q(10)
    L = lo if lo is not None else -cb - 1
    H = hi if hi is not None else cb + 1
    if L > H:
        L, H = H, L
    out = []
    if lo is not None:
        out.append(lo)
    if hi is not None:
        out.append(hi)
    if lo is None:
        out += [-cb - 1, -(cb + 1) * 1000]
    if hi is None:
        out += [cb + 1, (cb + 1) * 1000]
    if L == H or len(a) < 2:
        return out
    der = trim([i * a[i] for i in range(1, len(a))])
    for poly in (a, der):
        if len(poly) < 2:
            continue
        for l, h in _brackets(poly, L, H):
            out += [l, h, (l + h) / 2]
            for den in (10, 1000, 10 ** 6, 10 ** 12):
                out.append(((l + h) / 2).limit_denominator(den))
    return out


def snap(v, d):
    """Admissible readings nearest to v (both lattice neighbours)."""
    first, last, st = d
    if isinstance(v, float):
        return []
    res = []
    if st is None:
        cands = [v]
    else:
        k = v / st
        cands = [Q(math.floor(k)) * st, Q(math.ceil(k)) * st]
    for c in cands:
        if (isinstance(first, float) or c >= first) and (isinstance(last, float) or c <= last):
            res.append(c)
    if not res:
        if not isinstance(first, float) and v < first:
            res.append(first)
        if not isinstance(last, float) and v > last:
            res.append(last)
    return res


def var_candidates(d, rnd):
    first, last, st = d
    c = []
    fl, fh = not isinstance(first, float), not isinstance(last, float)
    if fl:
        c.append(first)
    if fh:
        c.append(last)
    if first == last:
        return c
    unit = st if st is not None else None
    if fl:
        c.append(first + (unit if unit else (Q(1, 1000) if not fh else (last - first) / 1000)))
    if fh:
        c.append(last - (unit if unit else (Q(1, 1000) if not fl else (last - first) / 1000)))
    if fl and fh:
        c.append((first + last) / 2)
        c.append(first + (last - first) / 3)
    for v in (0, 1, -1, 2, -2, Q(1, 2), Q(-1, 2), Q(1, 3), Q(-1, 3), Q(2, 3),
              Q(3, 2), Q(-3, 2), 3, -3, 5, 10, -10):
        c.append(Q(v))
    lo = first if fl else (last - 10 ** rnd.randint(1, 6) if fh else Q(-10 ** rnd.randint(1, 6)))
    hi = last if fh else (first + 10 ** rnd.randint(1, 6) if fl else Q(10 ** rnd.randint(1, 6)))
    for _ in range(5):
        den = rnd.choice([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 100, 997])
        c.append(lo + (hi - lo) * Q(rnd.randint(0, den), den))
    if not fl:
        c += [Q(-10) ** 3, Q(-10) ** 9]
    if not fh:
        c += [Q(10) ** 3, Q(10) ** 9]
    out = []
    for v in c:
        out += snap(Q(v), d)
    return sorted(set(out))


def gold_check(kind, e1, e2, specs, verdict, rnd):
    """Try to falsify a forced verdict. Returns (label, finding) where label
    is exact-enum / exact-lines / searched and finding is None or
    {"reading": {...}, "truth": ..., "why": ...}."""
    x1, x2, vs = expand(e1, e2, specs)
    doms = {}
    for v, s in vs.items():
        d = dom(s)
        if d is None:
            return "empty", {"why": "vacuous: a name in the claim has no admissible reading",
                             "reading": {}, "name": v}
        doms[v] = d
    names = sorted(vs)
    goal = goal_of(kind, verdict)
    want = verdict == "F"

    def test(env):
        t = gtruth(kind, x1, x2, env)
        if t == "undef":
            return {"reading": env, "truth": "undef",
                    "why": "the claim is undefined at an admissible reading"}
        if t is want:
            return {"reading": env, "truth": t, "why": "counterexample"}
        return None

    def report(f):
        r = {k: str(v) for k, v in f["reading"].items()}
        return dict(f, reading=r)

    if not names:
        f = test({})
        return "exact-enum", (report(f) if f else None)
    sizes = [dom_size(doms[v]) for v in names]
    total = 1
    for s in sizes:
        total *= s
    # ---- exact-enum
    if total <= ENUM_MAX:
        undef = None
        for pt in itertools.product(*[dom_points(doms[v]) for v in names]):
            f = test(dict(zip(names, pt)))
            if f and f["truth"] != "undef":
                return "exact-enum", report(f)
            undef = undef or f
        return "exact-enum", (report(undef) if undef else None)
    try:
        P = mpoly(("sub", x1, x2))
    except (NotPoly, Undef):
        P = None
    # ---- exact-lines
    if P is not None:
        for line in sorted(names, key=lambda v: -min(dom_size(doms[v]), 10 ** 12)):
            others = [v for v in names if v != line]
            n_fix = 1
            for v in others:
                n_fix *= dom_size(doms[v])
            if n_fix > LINE_FIX_MAX:
                continue
            if any(k > 2 for m in P for u, k in m if u == line):
                continue
            try:
                for pt in itertools.product(*[dom_points(doms[v]) for v in others]):
                    env = dict(zip(others, pt))
                    a = restrict(P, env, line)
                    t = line_exact(a, doms[line], goal)
                    if t is not None:
                        env[line] = t
                        f = test(env)
                        if f:
                            return "exact-lines", report(f)
                        raise AssertionError(f"line witness did not verify: {env}")
                return "exact-lines", None
            except NotPoly:
                continue
    # ---- searched
    cands = {v: var_candidates(doms[v], rnd) for v in names}
    readings = []
    prod = 1
    for v in names:
        prod *= len(cands[v])
    if prod <= 600:
        readings = [dict(zip(names, pt)) for pt in itertools.product(*[cands[v] for v in names])]
    else:
        for _ in range(400):
            readings.append({v: rnd.choice(cands[v]) for v in names})
    best = []
    for env in readings:
        f = test(env)
        if f:
            return "searched", report(f)
        if P is not None:
            try:
                d = gev(("sub", x1, x2), env)[0]
            except (Undef, Undecided):
                continue
            best.append((abs(d) if goal in ("d==0",) else (d if goal in ("d<=0", "d<0") else -d), env))
    if P is None:
        return "searched", None
    # quadratic faces: every name at lo / hi / free, gradient = 0 on the free
    tdeg = max((sum(k for _, k in m) for m in P), default=0)
    if tdeg <= 2 and len(names) <= 4:
        f = _faces(P, names, doms, test)
        if f:
            return "searched", report(f)
    # coordinate lines from the best readings
    best.sort(key=lambda z: z[0])
    starts = [e for _, e in best[:3]] or readings[:1]
    for env0 in starts:
        env = dict(env0)
        for _round in range(2):
            for v in names:
                a = restrict(P, env, v)
                for t in line_candidates(a, doms[v]):
                    for s in snap(Q(t), doms[v]):
                        e2 = dict(env)
                        e2[v] = s
                        f = test(e2)
                        if f:
                            return "searched", report(f)
                # move to the best point along the line
                bv, bs = None, None
                for t in line_candidates(a, doms[v]):
                    for s in snap(Q(t), doms[v]):
                        dv = peval(a, s)
                        sc = abs(dv) if goal == "d==0" else (dv if goal in ("d<=0", "d<0") else -dv)
                        if bv is None or sc < bv:
                            bv, bs = sc, s
                if bs is not None:
                    env[v] = bs
    return "searched", None


def _solve(A, b):
    n = len(A)
    M = [row[:] + [bb] for row, bb in zip(A, b)]
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None:
            return None
        M[c], M[p] = M[p], M[c]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c] / M[c][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [M[i][n] / M[i][i] for i in range(n)]


def _faces(P, names, doms, test):
    """Critical points of a quadratic on every face of the box."""
    choices = []
    for v in names:
        f, l, _ = doms[v]
        ch = ["free"]
        if not isinstance(f, float):
            ch.append(f)
        if not isinstance(l, float) and l != f:
            ch.append(l)
        choices.append(ch)
    for pick in itertools.product(*choices):
        fixed = {v: p for v, p in zip(names, pick) if p != "free"}
        free = [v for v in names if v not in fixed]
        if not free:
            continue
        # gradient of P restricted: dP/dv = sum over monomials
        A = [[Q(0)] * len(free) for _ in free]
        b = [Q(0)] * len(free)
        for m, c in P.items():
            pw = dict(m)
            for i, v in enumerate(free):
                if v not in pw:
                    continue
                k = pw[v]
                rest = dict(pw)
                rest[v] = k - 1
                coef = c * k
                lin = None
                for u, p in rest.items():
                    if p == 0:
                        continue
                    if u in fixed:
                        coef *= fixed[u] ** p
                    elif p == 1 and lin is None:
                        lin = u
                    else:
                        coef = None
                        break
                if coef is None:
                    break
                if lin is None:
                    b[i] -= coef
                else:
                    A[i][free.index(lin)] += coef
        sol = _solve(A, b)
        if sol is None:
            continue
        opts = []
        for v, x in zip(free, sol):
            opts.append(snap(x, doms[v]))
        if any(not o for o in opts):
            continue
        for pt in itertools.product(*opts):
            env = dict(fixed)
            env.update(zip(free, pt))
            f = test(env)
            if f:
                return f
    return None


# =============================================================== generators
TYPES_ALL = ["int", ("decimal", 1), ("decimal", 2), ("frac", 2), ("frac", 3),
             ("frac", 4), ("frac", 7), None]
CONSTS = ([Q(k) for k in range(-6, 7)] +
          [Q(1, 2), Q(-1, 2), Q(1, 3), Q(-2, 3), Q(3, 4), Q(-5, 7), Q(1, 10),
           Q(-3, 2), Q(5, 2), Q(1, 100), Q(7, 3)])
BIGC = [Q(1000), Q(-999), Q(10) ** 6, Q(1, 1000)]


def gen_const(rnd, big=False):
    if big and rnd.random() < 0.2:
        return rnd.choice(BIGC)
    return rnd.choice(CONSTS)


def gen_expr(rnd, depth, names, ops, p_name=0.65, p_leaf=0.25, big=False):
    if depth == 0 or rnd.random() < p_leaf:
        return rnd.choice(names) if rnd.random() < p_name else gen_const(rnd, big)
    op = rnd.choice(ops)
    if op == "sqrt":
        return ("sqrt", gen_expr(rnd, depth - 1, names, ops, p_name, p_leaf, big))
    if op == "sum":
        return ("sum", [gen_expr(rnd, depth - 1, names, ops, p_name, p_leaf, big)
                        for _ in range(rnd.randint(1, 3))])
    return (op, gen_expr(rnd, depth - 1, names, ops, p_name, p_leaf, big),
            gen_expr(rnd, depth - 1, names, ops, p_name, p_leaf, big))


def gen_box(rnd, discrete, style="small"):
    st = step_of(discrete)
    if style == "inf":
        r = rnd.random()
        base = gen_box(rnd, discrete, "small")
        if r < 0.35:
            return -INF, base[1]
        if r < 0.7:
            return base[0], INF
        return -INF, INF
    if style == "big":
        e = rnd.choice([3, 4, 6, 9])
        lo = rnd.randint(-10 ** e, 10 ** e)
        return Q(lo), Q(lo + rnd.randint(0, 2 * 10 ** e))
    if st is None or style == "wide":
        lo = rnd.choice(CONSTS[:13] + [Q(-1, 2), Q(1, 3), Q(-7, 4)])
        w = rnd.choice([Q(0), Q(1, 3), Q(1, 2), Q(1), Q(2), Q(5), Q(12)])
        return lo, lo + w
    k = rnd.randint(-12, 12)
    w = rnd.choice([0, 0, 1, 2, 3, 5, 8, 12, 20])
    lo, hi = st * k, st * (k + w)
    if st == 1 and rnd.random() < 0.3:
        lo, hi = lo * rnd.choice([1, 1, 1, 2]), hi * rnd.choice([1, 1, 1, 2]) + w
    if rnd.random() < 0.12:                  # a bound off the lattice
        lo = lo - st / 3
    if rnd.random() < 0.12:
        hi = hi + st / 2
    if lo > hi:
        lo, hi = hi, lo
    return Q(lo), Q(hi)


def mk_specs(rnd, names, types, box="small", p_pin=0.0, p_sample=0.0, p_inf=0.0):
    specs = {}
    for n in names:
        t = rnd.choice(types)
        style = "inf" if rnd.random() < p_inf else box
        lo, hi = gen_box(rnd, t, style)
        if rnd.random() < p_pin and not isinstance(lo, float):
            hi = lo
        specs[n] = {"lo": lo, "hi": hi, "discrete": t,
                    "sample": rnd.random() < p_sample}
    return specs


KINDS = ["le", "lt", "eq"]
NAMES = ["x", "y", "z"]


def gen_generic(rnd, types, ops, box="small", p_pin=0.1, p_sample=0.0,
                p_inf=0.0, big=False, max_names=3):
    k = rnd.randint(1, max_names)
    names = NAMES[:k]
    specs = mk_specs(rnd, names, types, box, p_pin, p_sample, p_inf)
    d1, d2 = rnd.randint(0, 3), rnd.randint(0, 3)
    e1 = gen_expr(rnd, d1, names, ops, big=big)
    e2 = gen_expr(rnd, d2, names, ops, big=big)
    return rnd.choice(KINDS), e1, e2, specs


def gen_intref(rnd):
    """The integer refinement's own territory: 1-2 int names, a degree-2
    polynomial split between the sides, small and huge boxes."""
    k = rnd.choice([1, 2, 2])
    names = NAMES[:k]
    style = rnd.choice(["small", "small", "big"])
    specs = {}
    for n in names:
        lo, hi = gen_box(rnd, "int", style)
        if rnd.random() < 0.1:
            hi = lo
        specs[n] = {"lo": lo, "hi": hi, "discrete": "int", "sample": False}
    mons = [()] + [((n, 1),) for n in names] + [((n, 2),) for n in names]
    if k == 2:
        mons += [(("x", 1), ("y", 1))]
        if rnd.random() < 0.15:
            mons += [(("x", 2), ("y", 1)), (("x", 1), ("y", 2))]
    cs = [Q(c) for c in range(-5, 6)] + [Q(1, 2), Q(-3, 2), Q(10), Q(-12), Q(97)]

    def mono(m):
        e = None
        for n, p in m:
            for _ in range(p):
                e = n if e is None else ("mul", e, n)
        return e

    def side():
        e = None
        for m in mons:
            if rnd.random() < 0.45:
                c = rnd.choice(cs)
                t = c if not m else (mono(m) if c == 1 else ("mul", c, mono(m)))
                e = t if e is None else (rnd.choice(["add", "sub"]), e, t)
        return e if e is not None else rnd.choice(cs)
    return rnd.choice(KINDS), side(), side(), specs


def gen_upoly(rnd):
    t = rnd.choice([None, None, "int", ("decimal", 1), ("frac", 3)])
    lo, hi = gen_box(rnd, t, rnd.choice(["small", "small", "inf"]))
    specs = {"x": {"lo": lo, "hi": hi, "discrete": t, "sample": False}}
    # a product of 3..8 linear factors (x - r), times a constant, plus noise
    roots = [rnd.choice(CONSTS) for _ in range(rnd.randint(3, 6))]
    e = rnd.choice(CONSTS[1:])
    for r in roots:
        e = ("mul", e, ("sub", "x", r))
    if rnd.random() < 0.5:
        e = ("add", e, gen_expr(rnd, 2, ["x"], ["add", "sub", "mul"]))
    other = gen_const(rnd) if rnd.random() < 0.6 else gen_expr(rnd, 2, ["x"], ["add", "mul"])
    return rnd.choice(KINDS), e, other, specs


UNITS = [None, None, "m", "kg", "m2", "m/kg"]


def gen_units(rnd):
    kind, e1, e2, specs = gen_generic(rnd, TYPES_ALL, ["add", "sub", "mul", "div", "sqrt"])
    for s in specs.values():
        s["unit"] = rnd.choice(UNITS)
    return kind, e1, e2, specs


def gen_edge(rnd):
    """Pinned ends, pinned at infinity, empty lattices, inverted bounds."""
    kind, e1, e2, specs = gen_generic(rnd, TYPES_ALL, ["add", "sub", "mul"], p_pin=0.3)
    for n, s in specs.items():
        r = rnd.random()
        if r < 0.15:
            s["lo"] = s["hi"] = rnd.choice([INF, -INF])
            s["discrete"] = None
        elif r < 0.3 and s["discrete"] is not None:
            st = step_of(s["discrete"])
            s["lo"] = s["hi"] = st / 2 if st != Q(1, 2) else Q(1, 3)
    return kind, e1, e2, specs


FRAGMENTS = {
    "int":     lambda r: gen_generic(r, ["int"], ["add", "sub", "mul"]),
    "intref":  gen_intref,
    "decimal": lambda r: gen_generic(r, [("decimal", 1), ("decimal", 2)], ["add", "sub", "mul"]),
    "frac":    lambda r: gen_generic(r, [("frac", m) for m in (2, 3, 4, 6, 7)], ["add", "sub", "mul"]),
    "cont":    lambda r: gen_generic(r, [None], ["add", "sub", "mul"]),
    "mixed":   lambda r: gen_generic(r, TYPES_ALL, ["add", "sub", "mul", "div", "sqrt"], p_pin=0.25, big=True),
    "sample":  lambda r: gen_generic(r, TYPES_ALL, ["add", "sub", "mul"], p_sample=0.5),
    "inf":     lambda r: gen_generic(r, TYPES_ALL, ["add", "sub", "mul", "div", "sqrt"], p_inf=0.6),
    "fine":    lambda r: gen_generic(r, [("decimal", 6), ("decimal", 30), ("frac", 997), ("frac", 10 ** 9)],
                                     ["add", "sub", "mul", "div"], p_pin=0.2,
                                     box=r.choice(["small", "wide"])),
    "sqrtdiv": lambda r: gen_generic(r, TYPES_ALL, ["add", "sub", "mul", "div", "div", "sqrt", "sqrt"]),
    "sum":     lambda r: gen_generic(r, TYPES_ALL, ["add", "sub", "mul", "sum", "sum"]),
    "upoly":   gen_upoly,
    "units":   gen_units,
    "edge":    gen_edge,
}
DEFAULT_N = {"int": 900_000, "intref": 700_000, "decimal": 450_000,
             "frac": 450_000, "cont": 700_000, "mixed": 500_000,
             "sample": 400_000, "inf": 350_000, "sqrtdiv": 450_000,
             "sum": 250_000, "upoly": 150_000, "units": 100_000,
             "edge": 100_000, "fine": 150_000, "doc": 120_000,
             "docmin": 60_000}


# ============================================================ the judge
def build(specs):
    import znum
    return {n: znum.qty(s["lo"], s["hi"], discrete=s["discrete"],
                        unit=s.get("unit"), sample=s.get("sample", False))
            for n, s in specs.items()}


def judge(kind, e1, e2, specs):
    """(verdict, ms). An exception is a refusal, recorded as 'EXC:<type>'."""
    import znum
    try:
        qs = build(specs)
    except Exception as exc:                   # noqa: BLE001 — recorded, not hidden
        return "EXC(qty):" + type(exc).__name__, 0.0
    t0 = time.perf_counter()
    try:
        v = znum.compare(kind, e1, e2, qs)[0]
    except Exception as exc:                   # noqa: BLE001 — recorded, not hidden
        v = "EXC:" + type(exc).__name__
    return v, (time.perf_counter() - t0) * 1000


def unit_dims(e, specs):
    """The judge's declared unit rule, re-derived: exponent maps, a
    dimensionless side unifies with anything, named units must match for
    + - and comparison. Returns a dim or raises ValueError."""
    def um(u):
        if not u:
            return {}
        out, sign = {}, 1
        for part in u.replace("/", " / ").split():
            if part == "/":
                sign = -1
                continue
            base = part.rstrip("0123456789")
            p = int(part[len(base):] or 1)
            out[base] = out.get(base, 0) + sign * p
            sign = 1
        return {k: v for k, v in out.items() if v}

    def uni(a, b):
        if not a:
            return b
        if not b or a == b:
            return a
        raise ValueError("unit")

    def w(e):
        if isinstance(e, Q):
            return {}
        if isinstance(e, str):
            return um(specs[e].get("unit"))
        if e[0] == "sum":
            d = {}
            for a in e[1]:
                d = uni(d, w(a))
            return d
        if e[0] == "sqrt":
            d = w(e[1])
            if any(p % 2 for p in d.values()):
                raise ValueError("odd")
            return {k: p // 2 for k, p in d.items()}
        a, b = w(e[1]), w(e[2])
        if e[0] in ("add", "sub"):
            return uni(a, b)
        s = 1 if e[0] == "mul" else -1
        out = dict(a)
        for k, p in b.items():
            out[k] = out.get(k, 0) + s * p
        return {k: p for k, p in out.items() if p}
    return w(e)


def show(e):
    if isinstance(e, Q):
        return str(e)
    if isinstance(e, str):
        return e
    if e[0] == "sum":
        return "sum(" + ", ".join(show(a) for a in e[1]) + ")"
    if e[0] == "sqrt":
        return f"sqrt({show(e[1])})"
    return f"({show(e[1])} {dict(add='+', sub='-', mul='*', div='/')[e[0]]} {show(e[2])})"


def show_specs(specs):
    out = {}
    for n, s in specs.items():
        lo = s["lo"] if isinstance(s["lo"], float) else str(s["lo"])
        hi = s["hi"] if isinstance(s["hi"], float) else str(s["hi"])
        out[n] = {"lo": str(lo), "hi": str(hi), "discrete": s["discrete"],
                  **({"sample": True} if s.get("sample") else {}),
                  **({"unit": s["unit"]} if s.get("unit") else {})}
    return out


# ============================================================ doc path
def render(e):
    if isinstance(e, Q):
        s = str(abs(e))
        s = s if "/" not in s else f"({s})"
        return s if e >= 0 else f"(0-{s})"
    if isinstance(e, str):
        return e
    if e[0] == "sum":
        return "sum(" + ",".join(render(a) for a in e[1]) + ")"
    if e[0] == "sqrt":
        return f"sqrt({render(e[1])})"
    sym = dict(add="+", sub="-", mul="*", div="/")[e[0]]
    return f"({render(e[1])} {sym} {render(e[2])})"


PREC = {"add": 1, "sub": 1, "mul": 2, "div": 2}


def render_min(e):
    """Minimal parentheses, standard precedence, left-associative: tests the
    ZFL reader's own precedence (`a - b - c`, `a / b * c`, `a - b + c`)."""
    if isinstance(e, Q):
        s = str(abs(e))
        s = s if "/" not in s else f"({s})"
        return s if e >= 0 else f"(-{s})"
    if isinstance(e, str):
        return e
    if e[0] == "sum":
        return "sum(" + ",".join(render(a) for a in e[1]) + ")"
    if e[0] == "sqrt":
        return f"sqrt({render_min(e[1])})"
    sym = dict(add="+", sub="-", mul="*", div="/")[e[0]]
    pr = PREC[e[0]]
    l, r = render_min(e[1]), render_min(e[2])
    if isinstance(e[1], tuple) and e[1][0] in PREC and PREC[e[1][0]] < pr:
        l = f"({l})"
    if isinstance(e[2], tuple) and e[2][0] in PREC and (
            PREC[e[2][0]] < pr or (PREC[e[2][0]] == pr and e[0] in ("sub", "div"))):
        r = f"({r})"
    return f"{l} {sym} {r}"


def _fmt_bound(v):
    if isinstance(v, float):
        return "inf" if v > 0 else "-inf"
    return str(v)


DOC_NAMES = {"x": "qa", "y": "qb", "z": "qc"}


def gen_doc(rnd):
    ops = rnd.choice([["add", "sub", "mul"], ["add", "sub", "mul", "div", "sqrt"],
                      ["add", "mul", "sum"]])
    types = ["int", ("decimal", 1), ("decimal", 2), ("frac", 3), ("frac", 4), None]
    kind, e1, e2, specs = gen_generic(rnd, types, [o for o in ops if o != "sum"],
                                      p_pin=0.15, p_sample=0.2, p_inf=0.1)
    if "sum" in ops:          # the reader takes sum(...) over plain names/numbers
        pool = list(specs) + [Q(1), Q(2), Q(0)]
        e1 = ("sum", [rnd.choice(pool) for _ in range(rnd.randint(1, 3))])
    ren = lambda e: (DOC_NAMES[e] if isinstance(e, str) else
                     e if isinstance(e, Q) else
                     ("sum", [ren(a) for a in e[1]]) if e[0] == "sum" else
                     ("sqrt", ren(e[1])) if e[0] == "sqrt" else (e[0], ren(e[1]), ren(e[2])))
    e1, e2 = ren(e1), ren(e2)
    specs = {DOC_NAMES[n]: s for n, s in specs.items()}
    return kind, e1, e2, specs


def doc_of(kind, e1, e2, specs, rnd, minimal=False):
    sym = {"le": "<=", "lt": "<", "eq": "=="}[kind]
    rd = render_min if minimal else render
    l, r = rd(e1), rd(e2)
    if kind != "eq" and rnd.random() < 0.3:        # the mirrored spellings
        sym = {"<=": ">=", "<": ">"}[sym]
        l, r = r, l
    rows = []
    for n, s in specs.items():
        val = (_fmt_bound(s["lo"]) if s["lo"] == s["hi"]
               else f"[{_fmt_bound(s['lo'])},{_fmt_bound(s['hi'])}]")
        t = s["discrete"]
        scale = ("" if t is None else "int" if t == "int" else
                 f"{t[0]}{t[1]}")
        verified = rnd.random() < 0.3
        rows.append({"name": n, "means": n, "value": val, "scale": scale,
                     "status": "verified" if verified else "unverified",
                     **({"ground": "doc-1"} if verified else {}),
                     **({"sample": True} if s.get("sample") else {})})
    return {"claim": f"{l} {sym} {r}", "rows": rows}


def doc_verdict(doc):
    import zfl
    t0 = time.perf_counter()
    try:
        out = zfl.run(doc)
    except Exception as exc:                   # noqa: BLE001
        return "EXC:" + type(exc).__name__, (time.perf_counter() - t0) * 1000
    ms = (time.perf_counter() - t0) * 1000
    if not out.get("ok"):
        return "REFUSED", ms
    num = (out.get("report") or {}).get("numeric")
    if not num:
        return "NO-NUMERIC", ms
    disp = num["disposition"]
    if disp == "EARNED":
        return "T", ms
    if disp == "REFUTED":
        return "F", ms
    if disp == "ON CREDIT":
        return {"toward T": "T", "toward F": "F"}.get(num.get("polarity"), "Z?"), ms
    if disp == "OPEN":
        return "Z", ms
    return disp, ms


# ============================================================== the runner
def run_chunk(args):
    frag, seed, k, n = args
    rnd = random.Random(f"{frag}:{seed}:{k}")
    grnd = random.Random(f"gold:{frag}:{seed}:{k}")
    counts = {"claims": 0, "T": 0, "F": 0, "Z": 0, "E": 0, "other": 0,
              "exact-enum": 0, "exact-lines": 0, "searched": 0,
              "lies": 0, "undef": 0, "vacuous": 0, "unit_verdicts": 0,
              "exc": {}}
    lies, notes, slow = [], [], []
    for i in range(n):
        if frag in ("doc", "docmin"):
            kind, e1, e2, specs = gen_doc(rnd)
            doc = doc_of(kind, e1, e2, specs, rnd, minimal=frag == "docmin")
            v, ms = doc_verdict(doc)
        else:
            kind, e1, e2, specs = FRAGMENTS[frag](rnd)
            v, ms = judge(kind, e1, e2, specs)
            doc = None
        counts["claims"] += 1
        if ms > SLOW_MS and frag not in ("doc", "docmin"):
            slow.append({"i": i, "chunk": k, "ms": round(ms, 1), "kind": kind,
                         "e1": show(e1), "e2": show(e2), "specs": show_specs(specs)})
        if v in ("T", "F", "Z", "E"):
            counts[v] += 1
        else:
            counts["other"] += 1
            counts["exc"][v] = counts["exc"].get(v, 0) + 1
            if len(notes) < 20:
                notes.append({"what": v, "kind": kind, "e1": show(e1), "e2": show(e2),
                              "specs": show_specs(specs), "chunk": k, "i": i})
        if v not in ("T", "F"):
            continue
        if any(s.get("unit") for s in specs.values()):
            try:
                a = unit_dims(e1, specs)
                b = unit_dims(e2, specs)
                if a and b and a != b:
                    raise ValueError("unit")
            except ValueError:
                counts["unit_verdicts"] += 1
                if len(notes) < 20:
                    notes.append({"what": "verdict on mismatched units", "verdict": v,
                                  "kind": kind, "e1": show(e1), "e2": show(e2),
                                  "specs": show_specs(specs), "chunk": k, "i": i})
                continue
        label, finding = gold_check(kind, e1, e2, specs, v, grnd)
        if label == "empty":
            counts["vacuous"] += 1
            if len(notes) < 20:
                notes.append({"what": "forced verdict on an empty reading set", "verdict": v,
                              "kind": kind, "e1": show(e1), "e2": show(e2),
                              "specs": show_specs(specs), "chunk": k, "i": i})
            continue
        counts[label] += 1
        if finding is None:
            continue
        rec = {"verdict": v, "kind": kind, "e1": show(e1), "e2": show(e2),
               "specs": show_specs(specs), "reading": finding["reading"],
               "truth": finding["truth"], "check": label, "chunk": k, "i": i,
               **({"doc": doc} if doc else {})}
        if finding["truth"] == "undef":
            counts["undef"] += 1
            if len(notes) < 20:
                notes.append(dict(rec, what="forced verdict, undefined at a reading"))
        else:
            counts["lies"] += 1
            if len(lies) < 25:
                lies.append(rec)
    return frag, k, counts, lies, notes, slow


# ============================================================ planted mode
# Pick an admissible reading r FIRST, then make the claim tight at r: with
# d = (e1 - e2)(r) exact, e2' = e2 + d, so e1 == e2' holds at r. Each base
# claim yields five, and r itself decides what each may NOT be:
#     e1 == e2'         true at r   -> F is a lie
#     e1 <= e2'         true at r   -> F is a lie
#     e1 <= e2' - δ     false at r  -> T is a lie
#     e1 <  e2'         false at r  -> T is a lie
#     e1 <  e2' + δ     true at r   -> F is a lie
# No search is involved: the witness is known before the judge is asked.
DELTAS = [Q(1), Q(1, 2), Q(1, 10 ** 9), Q(1, 10 ** 30)]


def planted_variants(kind_unused, e1, e2, specs, rnd):
    x1, x2, vs = expand(e1, e2, specs)
    env = {}
    for v, s in vs.items():
        d = dom(s)
        if d is None:
            return None, []
        env[v] = rnd.choice(var_candidates(d, rnd))
    try:
        a, b = gev(x1, env), gev(x2, env)
    except (Undef, Undecided):
        return None, []
    if a[0] != a[1] or b[0] != b[1]:
        return None, []                       # irrational at r: skip
    d = a[0] - b[0]
    dl = rnd.choice(DELTAS)
    e2p = ("add", e2, d) if d else e2
    return env, [("eq", e1, e2p, "F"), ("le", e1, e2p, "F"),
                 ("le", e1, ("sub", e2p, dl), "T"), ("lt", e1, e2p, "T"),
                 ("lt", e1, ("add", e2p, dl), "F")]


PLANTED = {"p-" + f: FRAGMENTS[f] for f in
           ("int", "intref", "decimal", "frac", "cont", "mixed", "sample",
            "inf", "sqrtdiv", "sum", "upoly", "fine", "units")}
PLANTED["p-doc"] = None
PLANTED["p-docmin"] = None
DEFAULT_N.update({"p-int": 300_000, "p-intref": 400_000, "p-decimal": 150_000,
                  "p-frac": 150_000, "p-cont": 300_000, "p-mixed": 250_000,
                  "p-sample": 200_000, "p-inf": 200_000, "p-sqrtdiv": 200_000,
                  "p-sum": 150_000, "p-upoly": 50_000, "p-fine": 100_000,
                  "p-units": 50_000, "p-doc": 60_000, "p-docmin": 60_000})


def run_planted_chunk(args):
    frag, seed, k, n = args
    rnd = random.Random(f"{frag}:{seed}:{k}")
    counts = {"claims": 0, "T": 0, "F": 0, "Z": 0, "E": 0, "other": 0,
              "planted_bases": 0, "lies": 0, "exc": {}}
    lies, notes, slow = [], [], []
    made = 0
    while made < n:
        if frag in ("p-doc", "p-docmin"):
            kind, e1, e2, specs = gen_doc(rnd)
        else:
            kind, e1, e2, specs = PLANTED[frag](rnd)
        env, variants = planted_variants(kind, e1, e2, specs, rnd)
        if not variants:
            continue
        counts["planted_bases"] += 1
        for kd, a, b, forbidden in variants:
            if made >= n:
                break
            made += 1
            if frag in ("p-doc", "p-docmin"):
                v, ms = doc_verdict(doc_of(kd, a, b, specs, rnd, minimal=frag == "p-docmin"))
            else:
                v, ms = judge(kd, a, b, specs)
            counts["claims"] += 1
            if v in ("T", "F", "Z", "E"):
                counts[v] += 1
            else:
                counts["other"] += 1
                counts["exc"][v] = counts["exc"].get(v, 0) + 1
            if ms > SLOW_MS and frag not in ("p-doc", "p-docmin"):
                slow.append({"i": made, "chunk": k, "ms": round(ms, 1), "kind": kd,
                             "e1": show(a), "e2": show(b), "specs": show_specs(specs)})
            if v == forbidden:
                # re-verify from the semantics before recording
                x1, x2, _ = expand(a, b, specs)
                t = gtruth(kd, x1, x2, env)
                if t is (forbidden == "F"):
                    counts["lies"] += 1
                    if len(lies) < 25:
                        lies.append({"verdict": v, "kind": kd, "e1": show(a), "e2": show(b),
                                     "specs": show_specs(specs),
                                     "reading": {x: str(y) for x, y in env.items()},
                                     "truth": t, "check": "planted", "chunk": k})
                else:
                    raise AssertionError(f"planted reading did not verify: {t} {show(a)} {show(b)} {env}")
    return frag, k, counts, lies, notes, slow


def _dispatch(p):
    return run_planted_chunk(p) if p[0].startswith("p-") else run_chunk(p)


def merge(acc, c):
    for key, v in c.items():
        if key == "exc":
            for kk, vv in v.items():
                acc["exc"][kk] = acc["exc"].get(kk, 0) + vv
        else:
            acc[key] = acc.get(key, 0) + v


def _parse_e(s, names):
    """Inverse of `show` for the slow-claim records."""
    s = s.strip()
    if s.startswith("sum("):
        inner, parts, depth, cur = s[4:-1], [], 0, ""
        for c in inner:
            depth += (c == "(") - (c == ")")
            if c == "," and depth == 0:
                parts.append(cur)
                cur = ""
            else:
                cur += c
        parts.append(cur)
        return ("sum", [_parse_e(p, names) for p in parts])
    if s.startswith("sqrt("):
        return ("sqrt", _parse_e(s[5:-1], names))
    if s.startswith("("):
        body, depth = s[1:-1], 0
        for i, c in enumerate(body):
            depth += (c == "(") - (c == ")")
            if depth == 0 and c == " " and body[i + 1] in "+-*/" and body[i + 2] == " ":
                op = dict(zip("+-*/", ("add", "sub", "mul", "div")))[body[i + 1]]
                return (op, _parse_e(body[:i], names), _parse_e(body[i + 3:], names))
        raise ValueError(s)
    return s if s in names else Q(s)


def _spec_back(sp):
    b = lambda v: -INF if v == "-inf" else INF if v == "inf" else Q(v)
    d = sp["discrete"]
    return {"lo": b(sp["lo"]), "hi": b(sp["hi"]),
            "discrete": tuple(d) if isinstance(d, list) else d,
            "sample": sp.get("sample", False), "unit": sp.get("unit")}


def _retime_one(s):
    import statistics
    import znum
    specs = {n: _spec_back(sp) for n, sp in s["specs"].items()}
    e1, e2 = _parse_e(s["e1"], specs), _parse_e(s["e2"], specs)
    qs = build(specs)
    ts = []
    for _ in range(5):
        t0 = time.perf_counter()
        znum.compare(s["kind"], e1, e2, qs)
        ts.append((time.perf_counter() - t0) * 1000)
    return statistics.median(ts), s


def retime(path, workers=1):
    d = json.load(open(path))
    if workers > 1:
        import multiprocessing as mp
        with mp.Pool(workers) as pool:
            rows = pool.map(_retime_one, d["slow"], chunksize=20)
    else:
        rows = [_retime_one(s) for s in d["slow"]]
    rows.sort(key=lambda r: -r[0])
    over = [r for r in rows if r[0] > SLOW_MS]
    print(f"{len(rows)} first-timing slow claims; {len(over)} stay > {SLOW_MS:g} ms "
          f"on re-timing (median of 5)")
    by = {}
    for ms, s in over:
        by[s["frag"]] = by.get(s["frag"], 0) + 1
    print("by fragment:", by)
    ms_all = sorted(r[0] for r in over)
    if ms_all:
        print(f"re-timed ms: median {ms_all[len(ms_all) // 2]:.1f}, max {ms_all[-1]:.1f}; "
              f"> 100 ms: {sum(1 for m in ms_all if m > 100)}, > 200 ms: "
              f"{sum(1 for m in ms_all if m > 200)}")
    for ms, s in over[:10]:
        print(f"  {ms:7.1f} ms  [{s['frag']}] {s['kind']} {s['e1']} ~ {s['e2']}  {s['specs']}")


def _desum(e):
    if isinstance(e, tuple):
        if e[0] == "sum":
            args = [_desum(a) for a in e[1]] or [Q(0)]
            out = args[0]
            for a in args[1:]:
                out = ("add", out, a)
            return out
        if e[0] == "sqrt":
            return ("sqrt", _desum(e[1]))
        return (e[0], _desum(e[1]), _desum(e[2]))
    return e


def attribute(path):
    """Every recorded lie: re-verify the refuting reading from the semantics,
    then spell each sum(...) as nested + (same claim, same readings) and
    re-judge. A lie that disappears is the sum's lattice step (LIE-1)."""
    d = json.load(open(path))
    tally = {}
    for frag, recs in d["lies"].items():
        for r in recs:
            specs = {n: _spec_back(sp) for n, sp in r["specs"].items()}
            e1, e2 = _parse_e(r["e1"], specs), _parse_e(r["e2"], specs)
            x1, x2, _ = expand(e1, e2, specs)
            env = {k: Q(v) for k, v in r["reading"].items()}
            ok = gtruth(r["kind"], x1, x2, env) is (r["verdict"] == "F")
            v, _ = judge(r["kind"], e1, e2, specs)       # direct compare()
            v2, _ = judge(r["kind"], _desum(e1), _desum(e2), specs)
            key = ("LIE-1 (sum)" if "sum" in r["e1"] + r["e2"] and v2 != r["verdict"]
                   else "UNATTRIBUTED")
            if not ok:
                key = "WITNESS DID NOT VERIFY"
            tally[(frag, key, v == r["verdict"])] = tally.get((frag, key, v == r["verdict"]), 0) + 1
    for (frag, key, same), n in sorted(tally.items()):
        print(f"  {frag:10s} {key:24s} compare() gives the same verdict: {same}  x{n}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", default="20260926")
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--chunk", type=int, default=2500)
    ap.add_argument("--only", default=None, help="comma-separated fragments")
    ap.add_argument("--n", type=int, default=None, help="claims per fragment")
    ap.add_argument("--scale", type=float, default=1.0)
    ap.add_argument("--out", default=None)
    ap.add_argument("--planted", action="store_true",
                    help="run the planted-reading fragments (p-*)")
    ap.add_argument("--attribute", default=None,
                    help="attribute every recorded lie of a result file")
    ap.add_argument("--retime", default=None,
                    help="re-time the slow claims of a result file (median of 5)")
    a = ap.parse_args()
    if a.retime:
        return retime(a.retime, a.workers)
    if a.attribute:
        return attribute(a.attribute)
    ap_planted = a.planted
    frags = (a.only.split(",") if a.only else
             list(PLANTED) if ap_planted else list(FRAGMENTS) + ["doc", "docmin"])
    plan = []
    for f in frags:
        n = a.n if a.n is not None else int(DEFAULT_N.get(f, 60_000) * a.scale)
        chunks = max(1, math.ceil(n / a.chunk))
        for k in range(chunks):
            plan.append((f, a.seed, k, min(a.chunk, n - k * a.chunk)))
    t0 = time.time()
    results = {f: {"exc": {}} for f in frags}
    lies, notes, slow = {f: [] for f in frags}, {f: [] for f in frags}, []
    if a.workers > 1:
        import multiprocessing as mp
        with mp.Pool(a.workers) as pool:
            it = pool.imap_unordered(_dispatch, plan)
            for j, (f, k, c, l, nt, sl) in enumerate(it, 1):
                merge(results[f], c)
                lies[f] += l
                notes[f] += nt
                slow += [dict(s, frag=f) for s in sl]
                if j % 50 == 0:
                    print(f"  {j}/{len(plan)} chunks, {time.time() - t0:.0f}s", flush=True)
    else:
        for p in plan:
            f, k, c, l, nt, sl = _dispatch(p)
            merge(results[f], c)
            lies[f] += l
            notes[f] += nt
            slow += [dict(s, frag=f) for s in sl]
    wall = time.time() - t0
    cols = (["claims", "planted_bases", "T", "F", "Z", "E", "other", "lies"]
            if any(f.startswith("p-") for f in frags) else
            ["claims", "T", "F", "Z", "E", "other", "exact-enum", "exact-lines",
             "searched", "lies", "undef", "vacuous", "unit_verdicts"])
    print(f"\nseed {a.seed}, {wall:.0f} s wall, {a.workers} workers")
    print("| fragment | " + " | ".join(cols) + " |")
    print("|---" * (len(cols) + 1) + "|")
    tot = {c: 0 for c in cols}
    for f in frags:
        r = results[f]
        print(f"| {f} | " + " | ".join(f"{r.get(c, 0):,}" for c in cols) + " |")
        for c in cols:
            tot[c] += r.get(c, 0)
    print("| **total** | " + " | ".join(f"{tot[c]:,}" for c in cols) + " |")
    for f in frags:
        if results[f]["exc"]:
            print(f"  {f}: refusals/exceptions {results[f]['exc']}")
    print(f"slow compare() calls (> {SLOW_MS:g} ms, first timing): {len(slow)}")
    for f in frags:
        for l in lies[f][:3]:
            print(f"  LIE [{f}] {l['verdict']} {l['kind']} {l['e1']} ~ {l['e2']} "
                  f"{l['specs']} reading {l['reading']} ({l['check']})")
    if a.out:
        with open(a.out, "w") as fh:
            json.dump({"seed": a.seed, "wall_s": wall, "results": results,
                       "lies": lies, "notes": notes, "slow": slow}, fh, indent=1,
                      default=str)


if __name__ == "__main__":
    main()
