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
grouped first order is proved in lean/ZEnergy.lean (2026-11-01, zero axioms): `target_first_grouped` — with d
constant on each part, |sum over all terms of g0 d T0 u0| <= sum_P t_P |sum_{e in P} g0 T0 u0| = D1. Trusses and
networks have one term per part and needed nothing new. And what the stand's network module (ztl-stand ustand/znet.py, 2026-10-11) left open — "trusses
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
# THE FLOATING PATH (2026-11-01): exact fractions grow to thousands of digits on large systems (a 1080-unknown frame
# took 151 s, ~n^3.3). The search solves in floats (trusted for nothing); the kernel checks, exactly:
#   1. the residuals r_u = f - K0 u~, r_y = e - K0 y~ (u~, y~ dyadic: short, no digit growth);
#   2. lam <= lambda_min(K0): K0 - lam I positive definite, by an INTERVAL LDL^T in integer fixed point (2^-bits,
#      every operation rounded outward) whose pivots all have positive lower ends;
#   3. then, in the K0-norm, ||u0 - u~|| <= ||r_u|| / sqrt(lam) (and y): the error's energy is r^T K0^-1 r;
#      e.u0 = e.u~ + y~.r_u + eps_y.r_u, |eps_y.r_u| = |eps_y^T K0 eps_u| <= ||eps_y|| ||eps_u||;
#      the first order's change from (y~, u~) to (y0, u0) is at most T (||eps_y|| ||u0|| + ||y~|| ||eps_u||)
#      (sum_P |x^T K_P z| <= ||x|| ||z|| by Cauchy-Schwarz over the PSD parts); the rest with ||u0|| <= ||u~|| + ||eps_u||.
# PROVED IN LEAN (lean/ZFloatPath.lean, 2026-11-01, zero axioms): `residual_energy` (lam B(eps,eps) <= |r|^2),
# `centre_identity` (e.u0 = e.u~ + y~.r_u + B(eps_y, eps_u), exact) and `centre_bound` (|B(eps_y, eps_u)| <= ey eu),
# `minkowski` (||u0|| <= ||u~|| + ||eps_u||), `first_order_fp` (the D1 above), `rest_fp` (the rest from ZNet's
# target_second). With ZRound's `pd_lower` for lam, the floating path cites only Higham 10.3 and the machine.

class _FX:
    """Integer fixed-point intervals: a value v is the pair (lo, hi) of integers with lo/2^b <= v <= hi/2^b."""
    def __init__(self, bits):
        self.b = bits
        self.one = 1 << bits

    def of(self, q):
        q = _q(q)
        n, d = q.numerator << self.b, q.denominator
        return (n // d, -((-n) // d))

    def sub(self, x, y):
        return (x[0] - y[1], x[1] - y[0])

    def mul(self, x, y):
        c = (x[0] * y[0], x[0] * y[1], x[1] * y[0], x[1] * y[1])
        return (min(c) >> self.b, -((-max(c)) >> self.b))

    def sq(self, x):
        lo, hi = x
        if lo >= 0:
            a, b = lo * lo, hi * hi
        elif hi <= 0:
            a, b = hi * hi, lo * lo
        else:
            a, b = 0, max(lo * lo, hi * hi)
        return (a >> self.b, -((-b) >> self.b))

    def div(self, x, y):
        if y[0] <= 0:
            raise ArithmeticError("division by an interval reaching zero")
        c = ((x[0] << self.b), (x[1] << self.b))
        cands = (c[0] // y[0], c[0] // y[1], c[1] // y[0], c[1] // y[1])
        cu = (-((-c[0]) // y[0]), -((-c[0]) // y[1]), -((-c[1]) // y[0]), -((-c[1]) // y[1]))
        return (min(cands), max(cu))


def pd_certificate(n, entries, lam, bits=192):
    """True iff K - lam I is proved positive definite by an interval LDL^T in fixed point (outward rounding): every
    pivot's lower end > 0. (False is not a refutation, only "not proved at these bits".)"""
    X = _FX(bits)
    cols = [dict() for _ in range(n)]
    for (i, j), v in entries.items():
        if i < j:
            i, j = j, i
        cols[j][i] = _q(v) + cols[j].get(i, Fr(0)) if i in cols[j] else _q(v)
    for j in range(n):
        cols[j][j] = cols[j].get(j, Fr(0)) - _q(lam)
        cols[j] = {i: X.of(v) for i, v in cols[j].items()}
    one2 = 1 << (2 * bits)
    for k in range(n):
        ck = cols[k]
        dk = ck.pop(k, (0, 0))
        if dk[0] <= 0:
            return False
        # 1/d_k once per column (MEASURED 2026-11-01: interval divisions were 35 s of 66 at 7200 unknowns)
        rk = (one2 // dk[1], -((-one2) // dk[0]))      # [1/d_hi, 1/d_lo] rounded outward
        rest = list(ck.items())
        cols[k] = {}
        scaled = [(i, X.mul(ai, rk)) for i, ai in rest]  # l_ik = a_ik / d_k
        for ii, (i, ai) in enumerate(rest):
            li = scaled[ii][1]
            for jj in range(ii + 1):                   # each unordered pair once (insertion order)
                j, aj = rest[jj]
                lo, hi = (j, i) if j <= i else (i, j)
                if i == j:                             # a_ik^2 / d_k: the square keeps the dependency
                    upd = X.mul(X.sq(ai), rk)
                else:
                    upd = X.mul(li, aj)               # (a_ik / d_k) a_jk
                col = cols[lo]
                col[hi] = X.sub(col.get(hi, (0, 0)), upd)
    return True


def pd_ieee(n, entries, mu):
    """lambda_min(K) >= the returned rational, by a FLOATING Cholesky (LAPACK, banded after reverse Cuthill-McKee)
    of A_f = fl(K - mu I) and Higham's backward-error theorem (2026-11-01, the curator's "Берем" to IEEE arithmetic
    as a NAMED premise):
      PREMISE (not proved here, not in Lean): IEEE 754 binary64, round to nearest, and LAPACK's Cholesky (any order
      of the inner products, FMA allowed). THEOREM USED (Higham, Accuracy and Stability of Numerical Algorithms,
      2nd ed. 2002, Thm 10.3, with Weyl's inequality): if the floating Cholesky of A_f runs to completion, the
      computed factor R satisfies R^T R = A_f + dA, |dA| <= g |R^T| |R|, g = gamma_{k+1} = (k+1)u/(1-(k+1)u) with
      k the longest inner product (k <= n; in a banded factorization k <= bw + 1, the rest exact zeros),
      u = 2^-53; and sum_k r_kj^2 <= a_jj/(1-g), so ||dA||_2 <= g/(1-g) tr(A_f), hence
      lambda_min(A_f) >= -g/(1-g) tr(A_f); and K - mu I = A_f + E with E computed EXACTLY here (the rounding of the
      entries), ||E||_2 <= ||E||_F. So lambda_min(K) >= mu - g/(1-g) tr(A_f) - ||E||_F.
    PROVED IN LEAN (lean/ZRound.lean, 2026-11-01, zero axioms): everything AFTER Higham's theorem — `pd_lower`:
      A_f + E = K - mu I, A_f + D = R^T R with |D_ij| <= g (|R|^T|R|)_ij, m + g = 1, sum E_ij^2 <= s^2 ==>
      0 <= m x^T(K - mu I)x + g tr(A_f)|x|^2 + m s |x|^2, i.e. x^T K x >= (mu - s - (g/m) tr A_f)|x|^2 — the lam
      returned (`chol_lower`: the Cholesky step; `weyl_frob`: the rounding of the entries). And Higham 10.3 itself,
      entry by entry, from the rounding model: lean/ZHigham.lean (2026-11-01, zero axioms) — `gamma_prod` (Lemma
      3.1), `telescope` (an accumulated sum, sequential), `cholesky_entry` (|(sum_k p_k + q) - a| <= g (sum |p_k|
      + |q|), g = gamma_N, the pivot's division or square root with its own factors). What stays a PREMISE: (1) the
      machine obeys the rounding model (IEEE 754 binary64, |delta| <= 2^-53, both forms (1+d) and 1/(1+d)); and that is
      all: ANY summation order is covered by `cholesky_entry_tree` (a summation tree — blocked dpbtrf, FMA and
      vector lanes included), and the coefficient used below is that theorem's g = (gamma_2 + 2 gamma_H)/(1 - gamma_H).
    Returns None if the Cholesky fails or the bound is not positive."""
    import numpy as np
    import scipy.sparse as sp
    from scipy.sparse.csgraph import reverse_cuthill_mckee
    from scipy.linalg import cholesky_banded, LinAlgError
    mu = _q(mu)
    rows, cols, vals = [], [], []
    for (i, j), v in entries.items():
        rows.append(i); cols.append(j)
        rows.append(j); cols.append(i)
    A = sp.csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(n, n))
    perm = reverse_cuthill_mckee(A, symmetric_mode=True)
    inv = np.empty(n, dtype=np.int64)
    inv[perm] = np.arange(n)
    bw = 0
    exact = {}
    for (i, j), v in entries.items():
        a, b = int(inv[i]), int(inv[j])
        if a < b:
            a, b = b, a
        exact[(a, b)] = exact.get((a, b), Fr(0)) + _q(v)
        bw = max(bw, a - b)
    for d in range(n):
        exact[(d, d)] = exact.get((d, d), Fr(0)) - mu
    ab = np.zeros((bw + 1, n))
    E2, tr = Fr(0), Fr(0)
    for (a, b), v in exact.items():
        fv = float(v)
        ab[a - b, b] = fv
        err = v - Fr(fv)
        E2 += err * err * (1 if a == b else 2)
        if a == b:
            tr += Fr(fv)
    try:
        cholesky_banded(ab, lower=True, overwrite_ab=True, check_finite=True)
    except (LinAlgError, ValueError):
        return None
    # gamma by the BAND, not by n: in a banded Cholesky every inner product has at most bw + 1 terms (the rest are
    # exact zeros, never computed), so Higham's gamma_{n+1} sharpens to gamma_{bw+2} (MEASURED 2026-11-01: with
    # gamma_{n+1} a 27900-unknown frame failed — the correction ~120 exceeded lambda_min ~40)
    u = Fr(1, 2 ** 53)
    # ANY summation order (lean/ZHigham.lean `cholesky_entry_tree`, 2026-11-01): an entry's accumulator is a tree
    # over at most H = bw + 2 leaves (the entry and the products in the band), the pivot's division or root two more
    # factors: the backward coefficient is g = (gamma_2 + 2 gamma_H)/(1 - gamma_H), a little over twice the
    # sequential gamma — the price of not trusting the library's order
    H = min(n, bw + 1) + 1
    gH = H * u / (1 - H * u)
    g2 = 2 * u / (1 - 2 * u)
    g = (g2 + 2 * gH) / (1 - gH)
    lam = mu - g / (1 - g) * max(tr, Fr(0)) - _sqrt_up(E2)
    return lam if lam > 0 else None


def _check_parts(parts):
    for p in parts:
        t = _q(p["t"])
        if not (0 <= t < 1):
            raise ValueError("a tolerance must be in [0, 1)")
        for w, g in p["terms"]:
            if _q(w) < 0:
                raise ValueError("a part's term has a negative weight: the part is not PSD as given")
    return max((_q(p["t"]) for p in parts), default=Fr(0))


def _float_matrix(K, n):
    import scipy.sparse as sp
    rows, cols_, vals = [], [], []
    for (i, j), v in K.items():
        rows.append(i); cols_.append(j); vals.append(float(v))
        if i != j:
            rows.append(j); cols_.append(i); vals.append(float(v))
    return sp.csc_matrix((vals, (rows, cols_)), shape=(n, n))


def _float_search(parts, f, e, n):
    import numpy as np
    import scipy.sparse.linalg as sla
    K = matrix(parts, n)
    A = _float_matrix(K, n)
    lu = sla.splu(A)
    u = lu.solve(np.array([float(x) for x in f]))
    y = lu.solve(np.array([float(x) for x in e]))
    try:
        lam = float(sla.eigsh(A, k=1, sigma=0, which="LM", return_eigenvectors=False, v0=np.ones(n))[0])
    except Exception:
        lam = float(min(A.diagonal())) * 1e-12
    return K, u, y, lam


def _kmul(K, x, n):
    r = [Fr(0)] * n
    for (i, j), v in K.items():
        r[i] += v * x[j]
        if i != j:
            r[j] += v * x[i]
    return r


def _fp_prepare(parts, f, n, bits=192, pd="ieee"):
    """The floating path's SHARED work, done once for any number of outputs (2026-11-01): the float factor, a
    proved lam, u~ with its exact residual and energy, and every term's g.u~."""
    import numpy as np
    import scipy.sparse.linalg as sla
    T = _check_parts(parts)
    K = matrix(parts, n)
    A = _float_matrix(K, n)
    lu = sla.splu(A)
    uf = lu.solve(np.array([float(x) for x in f]))
    try:
        lam_f = float(sla.eigsh(A, k=1, sigma=0, which="LM", return_eigenvectors=False, v0=np.ones(n))[0])
    except Exception:
        lam_f = float(min(A.diagonal())) * 1e-12
    if pd == "ieee":                                   # the floating Cholesky (named premise: IEEE 754's rounding)
        lam, used_bits = None, 0
        mu = Fr(lam_f) * Fr(9, 10) if lam_f > 0 else Fr(0)
        for _ in range(6):
            if mu > 0:
                lam = pd_ieee(n, K, mu)
            if lam:
                break
            mu /= 4
        if not lam:
            raise ArithmeticError("lambda_min(K0) not proved positive by the floating Cholesky")
    # the interval widths grow along the elimination: more bits first (MEASURED 2026-11-01: a 7200-unknown frame
    # was not proved at 192 bits, proved at 384 in 33 s), then a smaller lam
    else:
        lam = Fr(lam_f) / 2 if lam_f > 0 else Fr(0)
        proved, used_bits = False, bits
        if n > 4000 and bits < 384:                  # MEASURED: 7200 unknowns fail at 192, pass at 384
            bits = 384
        for _ in range(6):
            for b in (bits, 2 * bits, 4 * bits):
                if lam > 0 and pd_certificate(n, K, lam, b):
                    proved, used_bits = True, b
                    break
            if proved:
                break
            lam /= 4
        if not proved:
            raise ArithmeticError("lambda_min(K0) not proved positive: K0 may not be positive definite")
    ut = [Fr(float(x)) for x in uf]                     # dyadic: exact, short
    Ku = _kmul(K, ut, n)
    ru = [_q(f[i]) - Ku[i] for i in range(n)]
    eu = _sqrt_up(sum(x * x for x in ru) / lam)          # ||u0 - u~||_K0
    nu_t = _sqrt_up(sum(a * b for a, b in zip(ut, Ku)))   # ||u~||_K0
    gu = [[_dot(g, ut) for _, g in p["terms"]] for p in parts]
    return {"T": T, "K": K, "lu": lu, "n": n, "lam": lam, "bits": used_bits, "ut": ut, "ru": ru, "eu": eu,
            "nu_t": nu_t, "nu": nu_t + eu, "gu": gu}


def _fp_output(ctx, parts, e):
    """One output on a prepared floating path (see certify_output_fp)."""
    import numpy as np
    n, K, lam, T = ctx["n"], ctx["K"], ctx["lam"], ctx["T"]
    ut, ru, eu, nu_t, nu = ctx["ut"], ctx["ru"], ctx["eu"], ctx["nu_t"], ctx["nu"]
    yt = [Fr(float(x)) for x in ctx["lu"].solve(np.array([float(x) for x in e]))]
    Ky = _kmul(K, yt, n)
    ry = [_q(e[i]) - Ky[i] for i in range(n)]
    ey = _sqrt_up(sum(x * x for x in ry) / lam)
    ny_t = _sqrt_up(sum(a * b for a, b in zip(yt, Ky)))
    ny = ny_t + ey
    centre = sum(_q(a) * b for a, b in zip(e, ut)) + sum(a * b for a, b in zip(yt, ru))
    cerr = ey * eu
    signed, D1 = [], Fr(0)
    for p, gus in zip(parts, ctx["gu"]):
        c = sum(_q(w) * _dot(g, yt) * gv for (w, g), gv in zip(p["terms"], gus))
        signed.append(c)
        D1 += _q(p["t"]) * abs(c)
    slope_err = T * (ey * nu + ny_t * eu)               # >= sum_i t_i |slope_i(true) - slope_i(approx)|
    D1 += slope_err
    rest = T * T / (1 - T) * ny * nu if T else Fr(0)
    return {"nominal": centre, "nominal_err": cerr, "slope_err": slope_err,
            "lo": centre - cerr - D1 - rest, "hi": centre + cerr + D1 + rest,
            "first": D1, "rest": rest, "T": T, "slopes": [-c for c in signed], "lam": lam, "bits": ctx["bits"]}


def certify_output_fp(parts, f, e, n, bits=192, pd="ieee"):
    """As certify_output, without exact solves: floats searched, everything CHECKED exactly (see above).
    Returns the same keys (lo, hi, nominal as an interval midpoint, first, rest, T, slopes) plus 'lam'."""
    return _fp_output(_fp_prepare(parts, f, n, bits, pd), parts, e)


_MANY = {}


def _many_worker(idx):
    c = _MANY
    return idx, _fp_output(c["ctx"], c["parts"], c["es"][idx])


def certify_many(parts, f, es, n, jobs=1, exact_up_to=None):
    """Many outputs of ONE system (2026-11-01): the shared work once — the exact path's LDL^T and u0, or the floating
    path's factor, proved lam and u~ — and each output's own work (its y, residual, first order) per output, in
    `jobs` processes on the floating path. Results equal certify's, output by output."""
    if n <= (EXACT_UP_TO if exact_up_to is None else exact_up_to):
        return [certify_output(parts, f, e, n) for e in es] if len(es) <= 1 else _exact_many(parts, f, es, n)
    ctx = _fp_prepare(parts, f, n)
    if jobs <= 1 or len(es) <= 1:
        return [_fp_output(ctx, parts, e) for e in es]
    import multiprocessing as mp
    _MANY.clear()
    _MANY.update({"ctx": ctx, "parts": parts, "es": es})
    with mp.get_context("fork").Pool(min(jobs, len(es))) as pool:
        out = dict(pool.map(_many_worker, range(len(es))))
    _MANY.clear()
    return [out[i] for i in range(len(es))]


def _exact_many(parts, f, es, n):
    T = _check_parts(parts)
    K0 = matrix(parts, n)
    L, d = ldl(n, K0)
    u0 = solve(L, d, f)
    _check_solution(K0, u0, f)
    fu = sum(_q(a) * b for a, b in zip(f, u0))
    gu = [[_dot(g, u0) for _, g in p["terms"]] for p in parts]
    res = []
    for e in es:
        y0 = solve(L, d, e)
        _check_solution(K0, y0, e)
        nominal = sum(_q(ei) * ui for ei, ui in zip(e, u0))
        signed, D1 = [], Fr(0)
        for p, gus in zip(parts, gu):
            c = sum(_q(w) * _dot(g, y0) * gv for (w, g), gv in zip(p["terms"], gus))
            signed.append(c)
            D1 += _q(p["t"]) * abs(c)
        ey = sum(_q(a) * b for a, b in zip(e, y0))
        rest = T * T / (1 - T) * _sqrt_up(ey * fu) if T else Fr(0)
        res.append({"nominal": nominal, "lo": nominal - D1 - rest, "hi": nominal + D1 + rest,
                    "first": D1, "rest": rest, "T": T, "slopes": [-c for c in signed]})
    return res


def scaled_from(r, parts, k):
    """certify_scaled's range from an already certified output r (certify or certify_many)."""
    centre = r["nominal"]
    cerr = r.get("nominal_err", Fr(0))
    serr = r.get("slope_err", Fr(0))
    tk = _q(parts[k]["t"])
    D1p = Fr(0)
    for i, (p, sl) in enumerate(zip(parts, r["slopes"])):
        D1p += _q(p["t"]) * abs(sl + (centre if i == k else 0))
    half = cerr + D1p + serr + tk * cerr + tk * r["first"] + r["rest"] * (1 + tk)
    return {"nominal": centre, "lo": centre - half, "hi": centre + half, "base": r}


def value_enclosure_fp(parts, f, e, n, ps, bits=192):
    """[lo, hi] containing e^T u at the point p (the floating path at that point: every part fixed, t = 0)."""
    scaled = [{"t": 0, "terms": [(_q(w) * _q(pi), g) for w, g in p["terms"]]} for p, pi in zip(parts, ps)]
    r = certify_output_fp(scaled, f, e, n, bits)
    return r["lo"], r["hi"]


# Exact solves up to this many unknowns, the floating path above. MEASURED 2026-11-01: the floating path gives the
# same widths to 4 digits and is faster from ~100 unknowns (plate 448: 0.05 s vs 28.6 s exact; frame 450: 0.03 s vs
# 4.2 s); it was 600 until the plates showed exact fractions growing faster than on frames (576 unknowns: 71 s).
EXACT_UP_TO = 120


def certify_scaled(parts, f, e, n, k, exact_up_to=None):
    """A proved range of p_k * (e . u(p)) — an output scaled by ONE part's own factor (a stress: E p_k D0 B u), with
    that factor merged into the exact first order instead of multiplied as an interval (2026-11-01):
        p_k w = w0 + [sum_i (s_i + w0 [i = k]) d_i] + d_k L + Sec (1 + d_k),   L = sum_i s_i d_i, |Sec| <= rest
    so  p_k w in centre +- (cerr + sum_i t_i |s~_i + centre [i = k]| + slope_err + t_k cerr + t_k first
    + rest (1 + t_k)), with s~ the (approximate) slopes, `first` >= |L| — every piece already proved (ZNet step 4,
    ZFloatPath's centre and first-order bounds)."""
    return scaled_from(certify(parts, f, e, n, EXACT_UP_TO if exact_up_to is None else exact_up_to), parts, k)


def certify(parts, f, e, n, exact_up_to=None):
    """The kernel's choice: exact solves up to EXACT_UP_TO unknowns, the floating path above (both proved)."""
    lim = EXACT_UP_TO if exact_up_to is None else exact_up_to
    return certify_output(parts, f, e, n) if n <= lim else certify_output_fp(parts, f, e, n)


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
    fp_cases = 0
    for trial in range(15):                             # the floating path must contain the exact one
        n, m = rng.randint(3, 8), rng.randint(2, 6)
        parts, f, e = _random_case(rng, n, m, Fr(rng.choice([1, 5, 20]), 100))
        a, b2 = certify_output(parts, f, e, n), certify_output_fp(parts, f, e, n)
        assert b2["lo"] <= a["lo"] and a["hi"] <= b2["hi"], (trial, a, b2)
        fp_cases += 1
    print(f"   floating path: {fp_cases} random systems, its proved range contains the exact path's every time")
    sc_pts = 0
    for trial in range(15):                             # p_k * (e.u) inside certify_scaled's range, everywhere tried
        n, m = rng.randint(2, 5), rng.randint(1, 4)
        parts, f, e = _random_case(rng, n, m, Fr(rng.choice([1, 5, 20]), 100))
        k = rng.randrange(len(parts))
        r = certify_scaled(parts, f, e, n, k)
        rf = certify_scaled(parts, f, e, n, k, exact_up_to=0)     # the floating path forced, on a small system
        assert rf["lo"] <= r["lo"] and r["hi"] <= rf["hi"], (trial, r, rf)
        pts = list(itertools.product(*[[1 - p["t"], 1 + p["t"]] for p in parts])) if len(parts) <= 8 else []
        pts += [[1 + p["t"] * Fr(rng.randint(-100, 100), 100) for p in parts] for _ in range(15)]
        for ps in pts:
            v = _q(ps[k]) * value_at(parts, f, e, n, ps)
            assert r["lo"] <= v <= r["hi"], (trial, v, r["lo"], r["hi"])
            sc_pts += 1
    for trial in range(6):                              # certify_many == certify, output by output, both paths
        n, m = rng.randint(3, 6), rng.randint(2, 5)
        parts, f, _ = _random_case(rng, n, m, Fr(rng.choice([1, 5, 20]), 100))
        es = [[Fr(1) if i == j else Fr(0) for i in range(n)] for j in range(n)]
        for path in (600, 0):
            many = certify_many(parts, f, es, n, jobs=2, exact_up_to=path)
            one = [certify(parts, f, e, n, exact_up_to=path) for e in es]
            assert [(a["lo"], a["hi"]) for a in many] == [(b["lo"], b["hi"]) for b in one], (trial, path)
    print("   certify_many: equal to certify output by output, exact and floating paths, 2 processes")
    print(f"   scaled outputs: {sc_pts} points, p_k (e.u) inside certify_scaled's range every time "
          f"(and the floating path's range contains the exact one's)")
    # the IEEE certificate agrees with the exact interval one, and is sharp: proves lam*0.9, refuses lam*1.01
    parts, f, e, n = _cantilever_demo(40)
    K = matrix(parts, n)
    lam_f = _float_search(parts, f, e, n)[3]
    agree = 0
    for fac in (Fr(1, 2), Fr(9, 10), Fr(101, 100), Fr(2)):
        a_ = pd_ieee(n, K, Fr(lam_f) * fac) is not None
        b_ = pd_certificate(n, K, Fr(lam_f) * fac, 384)
        assert a_ == b_ == (fac < 1), (fac, a_, b_)
        agree += 1
    print(f"   IEEE certificate (premise: IEEE 754 + LAPACK, Higham Thm 10.3): agrees with the exact interval one "
          f"{agree}/4, proves 0.9 lambda_min, refuses 1.01")
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
