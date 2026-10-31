"""PERTURBATION IN THE ENERGY NORM: a proved bound on one output of K(p) u = f, where the stiffness is a SUM OF
POSITIVE SEMIDEFINITE PARTS each scaled by its own factor p_i in [1 - t_i, 1 + t_i] (a kernel module, 2026-10-31).

WHY. zlin certifies A(p) x = b(p) for any square A, but its contraction is measured in the max-norm, where the
condition number multiplies every tolerance: on the IFEM cantilever (ztl-stand bench/stage0, 2026-10-31) a +2 %
requirement was proved at 81 unknowns in 7 s and not at 161 in 30 min, cond(K) growing ~k^4. For a stiffness (or a
conductance) matrix the right ruler is the matrix itself: with every part PSD and |delta_i| <= t_i <= T,
    -T K0  <=  Delta K  <=  T K0          (Loewner order)
so in the K0-norm the perturbation has size T WHATEVER cond(K0) is. The curator's course of 2026-10-31.

THE CLASS. K(p) = sum_i p_i K_i, each K_i = sum_j w_ij g_ij g_ij^T with w_ij >= 0 (a PSD part given as rank-one
terms: a bar's E A / L c c^T, a conductance, or any element matrix split by its own LDL^T); p_i in [1 - t_i, 1 + t_i],
0 <= t_i < 1, independently; K0 = K(1) symmetric positive definite (proved here: every pivot of its exact LDL^T > 0);
the load f and the output functional e are fixed rational vectors (a load range is the caller's superposition).

WHAT IS PROVED: for every p in the box,  e^T u(p)  in  [ e^T u0 - D1 - R ,  e^T u0 + D1 + R ]  with
    u0 = K0^-1 f,  y0 = K0^-1 e                                  (exact rational solves)
    D1 = sum_i t_i | sum_j w_ij (y0 . g_ij)(g_ij . u0) |          (the first order, exact: linear in each delta_i)
    R  = T^2/(1 - T) * sqrt( (e . y0)(f . u0) )                    (the rest; sqrt rounded UP to a rational)
and when the caller asks, a WITNESS: the vertex p_i = 1 - sgn(...) t_i that drives the first order up, solved
exactly — a point where e^T u is attained, for refuting a bound.

THE PROOF IS IN LEAN ALREADY (found 2026-11-01 — I had written "Lean pending", forgetting our own work): it is step 4
of the network certificate, lean/ZNet.lean (2026-10-12, zero axioms), stated for ANY vectors s_e, so it covers a
bar's elongation row as well as a branch's incidence:
  target_identity   the output's change = -(first order) - (second order), exact, from the equilibrium at p and the
                    reverse field L0 z0 = q (here y0, its exact residual checked);
  target_first      |first| <= sum_e g0_e t_e |T0_e| |u0_e|                    (= D1 for one-term parts);
  target_second     (1 - t)^2 Sec^2 <= (sum_e g0_e (t_e T0_e)^2)(sum_e g0_e (t_e u0_e)^2)
                    with T = max t_e this is <= (T^2/(1-T))^2 (e . y0)(f . u0)   (= R; ZNet's per-part form is
                    tighter, so R is covered);
  energy_perturbation, cs_weighted   the energy step and Cauchy-Schwarz with weights, squared, no roots.
What ZNet does NOT cover, said: a part of SEVERAL terms sharing one factor (a beam element split by its LDL^T): the
grouped first order t |sum_j x_j| <= sum_j t |x_j| is the other direction, so D1 grouped needs a one-line lemma
(d common to the terms: |d sum_j x_j| = |d| |sum_j x_j|) — to add when such parts are used; trusses and networks have
one term per part. And what the stand's network module (ztl-stand ustand/znet.py, 2026-10-11) left open — "trusses
have the same form with vector unknowns; there L is not an M-matrix and step 2 needs another certificate" — is what
this module supplies: an EXACT solve, its residual checked, instead of an approximate one with an eigenvalue bound.
The derivation, for the reader:
  e^T u - e^T u0 = e^T (K^-1 - K0^-1) f = -y^T DK u0  with y = K^-1 e (K symmetric), and y = y0 - K^-1 DK y0, so
  e^T u - e^T u0 = -y0^T DK u0 + y0^T DK K^-1 DK u0.
  The first term is sum_i delta_i (-sum_j w_ij (y0.g_ij)(g_ij.u0)); over |delta_i| <= t_i its range is exactly +-D1.
  For the second write M = K0^-1/2 DK K0^-1/2: -T I <= M <= T I gives ||M||_2 <= T, and K = K0^1/2 (I + M) K0^1/2,
  so y0^T DK K^-1 DK u0 = a^T M (I + M)^-1 M b with a = K0^1/2 y0, b = K0^1/2 u0, ||(I + M)^-1|| <= 1/(1 - T);
  hence |.| <= T^2/(1 - T) ||a|| ||b||, and ||a||^2 = y0^T K0 y0 = e . y0, ||b||^2 = u0^T K0 u0 = f . u0.
  The Loewner step: DK = sum_i delta_i K_i with K_i PSD, so T K0 - DK = sum_i (T - delta_i) K_i >= 0 and likewise
  T K0 + DK >= 0.

MEASURED (float prototype, the same cantilever): the bound is nominal +0.503 % at 41..1281 unknowns, the rest
0.0026 %; the IFEM benchmark's exact range at +-0.5 % moduli is about +-0.5 %.
"""
from fractions import Fraction as Fr
import math


def _q(x):
    return x if isinstance(x, Fr) else Fr(x)


def ldl(n, entries):
    """Exact LDL^T of the symmetric matrix {(i, j): v} (i >= j given once). Returns (rows, d) — rows[i] = {j: l_ij}
    for j < i — or raises ValueError if a pivot is not > 0 (K0 not positive definite). No pivoting: positive
    definiteness is exactly what makes every pivot > 0 in any order, so the check IS the certificate.
    Right-looking, column by column (fill-in lands in the columns it creates). The answer is not trusted: every
    solve is checked by its exact residual (_check_solution) — the first version of this function was wrong and
    that check, not the vertex test, caught it (2026-10-31)."""
    cols = [dict() for _ in range(n)]                  # cols[j][i] = a_ij, i >= j
    for (i, j), v in entries.items():
        if i < j:
            i, j = j, i
        cols[j][i] = cols[j].get(i, Fr(0)) + _q(v)
    d = [Fr(0)] * n
    rows = [dict() for _ in range(n)]
    for k in range(n):
        ck = cols[k]
        dk = ck.pop(k, Fr(0))
        if dk <= 0:
            raise ValueError(f"K0 is not positive definite: pivot {k} is {dk}")
        d[k] = dk
        lk = {i: a / dk for i, a in ck.items() if a}
        cols[k] = {}
        for i, li in lk.items():
            rows[i][k] = li
        for i, li in lk.items():                       # A[i][j] -= l_ik d_k l_jk for k < j <= i
            for j, lj in lk.items():
                if j <= i:
                    cols[j][i] = cols[j].get(i, Fr(0)) - li * lj * dk
    return rows, d


def solve(L, d, b):
    n = len(d)
    z = [_q(v) for v in b]
    for i in range(n):                                  # L z = b
        for j, lij in L[i].items():
            z[i] -= lij * z[j]
    x = [z[i] / d[i] for i in range(n)]                 # D
    cols = [[] for _ in range(n)]
    for i in range(n):
        for j, lij in L[i].items():
            cols[j].append((i, lij))
    for j in range(n - 1, -1, -1):                      # L^T x = z/D
        for i, lij in cols[j]:
            x[j] -= lij * x[i]
    return x


def _check_solution(K, x, b):
    """K x == b exactly (K given as its lower triangle) — the solver is not trusted, its answer is."""
    n = len(x)
    r = [Fr(0)] * n
    for (i, j), v in K.items():
        r[i] += v * x[j]
        if i != j:
            r[j] += v * x[i]
    bad = [i for i in range(n) if r[i] != _q(b[i])]
    if bad:
        raise ArithmeticError(f"exact residual nonzero at rows {bad[:5]}: the solve is wrong")


def _dot(g, v):
    return sum(c * v[i] for i, c in g.items())


def _sqrt_up(q):
    """A rational >= sqrt(q) for q >= 0, within one part in 10^12 of it."""
    if q <= 0:
        return Fr(0)
    num, den = q.numerator, q.denominator
    s = 10 ** 12
    r = math.isqrt(num * den * s * s)                   # floor(sqrt(num*den) * s)
    up = Fr(r + 1, den * s)                             # sqrt(num/den) = sqrt(num*den)/den
    assert up * up >= q
    return up


def matrix(parts, n):
    """K0 = sum over parts of sum_j w g g^T, as {(i, j): v} with i >= j."""
    K = {}
    for p in parts:
        for w, g in p["terms"]:
            items = list(g.items())
            for a, ga in items:
                for b, gb in items:
                    if a >= b:
                        K[(a, b)] = K.get((a, b), Fr(0)) + _q(w) * ga * gb
    return K


def certify_output(parts, f, e, n, want_witness=False):
    """parts: [{"t": tolerance, "terms": [(w, {dof: coeff}), ...]}, ...]; f, e: lists of n rationals.
    Returns {"nominal", "lo", "hi", "first", "rest", "T"} (and "witness": {"p": [...], "value": ...})."""
    for p in parts:
        t = _q(p["t"])
        if not (0 <= t < 1):
            raise ValueError("a tolerance must be in [0, 1)")
        for w, g in p["terms"]:
            if _q(w) < 0:
                raise ValueError("a part's term has a negative weight: the part is not PSD as given")
    T = max((_q(p["t"]) for p in parts), default=Fr(0))
    K0 = matrix(parts, n)
    L, d = ldl(n, K0)
    u0, y0 = solve(L, d, f), solve(L, d, e)
    _check_solution(K0, u0, f)
    _check_solution(K0, y0, e)
    nominal = sum(_q(ei) * ui for ei, ui in zip(e, u0))
    signed = []
    D1 = Fr(0)
    for p in parts:
        c = sum(_q(w) * _dot(g, y0) * _dot(g, u0) for w, g in p["terms"])
        signed.append(c)
        D1 += _q(p["t"]) * abs(c)
    ey, fu = sum(_q(a) * b for a, b in zip(e, y0)), sum(_q(a) * b for a, b in zip(f, u0))
    rest = T * T / (1 - T) * _sqrt_up(ey * fu) if T else Fr(0)
    out = {"nominal": nominal, "lo": nominal - D1 - rest, "hi": nominal + D1 + rest,
           "first": D1, "rest": rest, "T": T,
           "slopes": [-c for c in signed]}    # d(e.u)/d p_i at p = 1 (exact): e.u moves by +slope_i * delta_i
    if want_witness:
        # e^T u moves by -sum delta_i c_i to first order: up when delta_i = -sgn(c_i) t_i
        ps = [1 - (_q(p["t"]) if c > 0 else -_q(p["t"]) if c < 0 else 0) for p, c in zip(parts, signed)]
        out["witness"] = {"p": ps, "value": value_at(parts, f, e, n, ps)}
    return out


def value_at(parts, f, e, n, ps):
    """e^T u at the point p (exact)."""
    scaled = [{"t": 0, "terms": [(_q(w) * _q(pi), g) for w, g in p["terms"]]} for p, pi in zip(parts, ps)]
    K = matrix(scaled, n)
    L, d = ldl(n, K)
    u = solve(L, d, f)
    _check_solution(K, u, f)
    return sum(_q(ei) * ui for ei, ui in zip(e, u))


# ----------------------------------------------------------------------------------------------------------------
# self-test: against every vertex and random interior points; a mutation (the rest dropped) must be caught

def _random_case(rng, n, m, t):
    parts = []
    for _ in range(m):
        g = {}
        for _ in range(rng.randint(1, 3)):
            g[rng.randrange(n)] = Fr(rng.randint(-5, 5) or 1, rng.randint(1, 4))
        parts.append({"t": t, "terms": [(Fr(rng.randint(1, 6), rng.randint(1, 3)), g)]})
    for i in range(n):                                  # a grounding part per dof keeps K0 definite
        parts.append({"t": t, "terms": [(Fr(1, rng.randint(1, 5)), {i: Fr(1)})]})
    f = [Fr(rng.randint(-3, 3)) for _ in range(n)]
    e = [Fr(0)] * n
    e[rng.randrange(n)] = Fr(1)
    return parts, f, e


def _selftest():
    import itertools
    import random
    rng = random.Random(20261031)
    checked = cases = 0
    caught = False
    for trial in range(40):
        n, m = rng.randint(2, 5), rng.randint(1, 4)
        t = Fr(rng.choice([1, 5, 20, 50]), 100)
        parts, f, e = _random_case(rng, n, m, t)
        r = certify_output(parts, f, e, n)
        cases += 1
        pts = list(itertools.product(*[[1 - p["t"], 1 + p["t"]] for p in parts])) if len(parts) <= 9 else []
        pts += [[1 + p["t"] * Fr(rng.randint(-100, 100), 100) for p in parts] for _ in range(20)]
        for ps in pts:
            v = value_at(parts, f, e, n, ps)
            assert r["lo"] <= v <= r["hi"], (trial, v, r)
            checked += 1
            if not (r["nominal"] - r["first"] <= v <= r["nominal"] + r["first"]):
                caught = True                           # the rest is needed: without it this point escapes
    assert caught, "the mutation (rest dropped) was never caught: the self-test is too weak"
    print(f"   {cases} random systems, {checked} points (every vertex where <= 9 parts, plus 20 interior each):")
    print("   every value inside [lo, hi]; dropping the second-order rest lets a point escape (mutation caught)")


def _cantilever_demo(k=40):
    """The IFEM cantilever of ztl-stand (bench/hard-tasks/mkcant.py), exactly: k floors, E = A = 1, FX = 1 on the
    left nodes, every bar +-0.5 %."""
    nodes = {}
    for fl in range(k + 1):
        nodes[2 * fl + 1] = (Fr(0), Fr(3, 4) * fl)
        nodes[2 * fl + 2] = (Fr(1), Fr(3, 4) * fl)
    bars = []
    for fl in range(k):
        a, b, c, dd = 2 * fl + 1, 2 * fl + 2, 2 * fl + 3, 2 * fl + 4
        bars += [(a, c), (b, dd), (c, dd), (a, dd), (b, c)]
    bars.append((1, 2))
    fixed = {(1, 0), (1, 1), (2, 1)}
    dof = {}
    for nd in sorted(nodes):
        for ax in (0, 1):
            if (nd, ax) not in fixed:
                dof[(nd, ax)] = len(dof)
    parts = []
    for a, b in bars:
        (xa, ya), (xb, yb) = nodes[a], nodes[b]
        dx, dy = xb - xa, yb - ya
        L = {Fr(1): Fr(1), Fr(9, 16): Fr(3, 4), Fr(25, 16): Fr(5, 4)}[dx * dx + dy * dy]
        g = {}
        for (nd, ax), v in (((a, 0), -dx / L), ((a, 1), -dy / L), ((b, 0), dx / L), ((b, 1), dy / L)):
            if (nd, ax) in dof:
                g[dof[(nd, ax)]] = v
        parts.append({"t": Fr(1, 200), "terms": [(1 / L, g)]})
    n = len(dof)
    f = [Fr(0)] * n
    for fl in range(1, k + 1):
        f[dof[(2 * fl + 1, 0)]] += 1
    e = [Fr(0)] * n
    e[dof[(2 * k + 2, 0)]] = Fr(1)
    return parts, f, e, n


if __name__ == "__main__":
    import time
    print("=" * 72)
    print("ZENERGY — one output of a PSD-sum stiffness, bounded in the energy norm")
    print("=" * 72)
    _selftest()
    for k in (10, 40, 160):
        parts, f, e, n = _cantilever_demo(k)
        t0 = time.time()
        r = certify_output(parts, f, e, n, want_witness=k <= 40)
        dt = time.time() - t0
        rel = lambda x: float(x / r["nominal"]) * 100
        w = r.get("witness")
        print(f"   cantilever k={k:3d} ({n} unknowns): nominal {float(r['nominal']):.6g}, "
              f"upper +{rel(r['hi'] - r['nominal']):.4f} % (first {rel(r['first']):.4f}, rest {rel(r['rest']):.5f}), "
              f"{dt:.1f} s" + (f"; witness +{rel(w['value'] - r['nominal']):.4f} %" if w else ""))
        if w:
            assert r["lo"] <= w["value"] <= r["hi"]
    print("ZENERGY GREEN — every checked value inside the proved range; the rest is needed and bounded")
