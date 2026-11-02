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


SPARSE_CHOL_FROM = 1500      # unknowns from which pd_ieee / pd_ieee_float use CHOLMOD when it is installed


def _have_cholmod():
    try:
        import sksparse.cholmod  # noqa: F401
        return True
    except ImportError:
        return False


def _chol_sparse(n, hi, lo, vals):
    """The floating Cholesky by CHOLMOD (scikit-sparse; SUPERNODAL LL^T — LAPACK dpotrf / BLAS dtrsm, dsyrk, dgemm
    inside), in the caller's reverse Cuthill-McKee order: returns H, the longest inner product + 1 (the entry's own leaf), or
    None if it fails (not positive definite) or CHOLMOD is not installed. (2026-11-02, the space frames' size: a
    banded Cholesky costs n bw^2 and a 3D frame's band is a whole floor.) The theorem used is pd_ieee's: Higham's
    entry bound over ANY summation tree (lean/ZHigham `cholesky_entry_tree`) with H leaves; a symmetric permutation
    changes nothing (P A P^T has the same eigenvalues); an entry of L is (a_ij - sum_k l_ik l_jk) / l_jj over the k
    where row i AND row j of L are nonzero — at most (row count of L) - 1 products; supernodal padding adds products
    with an exact 0.0 factor, exact, no rounding. Returns (H, None) on success."""
    try:
        from sksparse.cholmod import cholesky, CholmodNotPositiveDefiniteError
    except ImportError:
        return "absent"
    import numpy as np
    import scipy.sparse as sp
    A = sp.csc_array((vals, (hi, lo)), shape=(n, n))     # the lower triangle (row >= column)
    try:
        import warnings
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            # order NATURAL: the input is already in reverse Cuthill-McKee order, so the factor's rows are at most the
            # band — H as the banded path's. MEASURED 2026-11-02 (a 21780-unknown space frame): fill-reducing orders
            # are faster still (1.3 s) but their longest row is 3846, not 733, and Higham's term grows with it (79 vs
            # 15 against a lambda_min ~ 79: the stability bound 2.7 % weaker); natural 2.3 s, banded dpbtrf 18.7 s
            L, _perm = cholesky(A, lower=True, order="natural", supernodal_mode="supernodal")
    except (CholmodNotPositiveDefiniteError, ArithmeticError, ValueError):
        return None
    except Exception:
        return None
    L = sp.csr_array(L)
    if not np.all(np.isfinite(L.data)) or np.any(L.diagonal() <= 0):
        return None
    rowcount = np.diff(L.indptr)
    return int(rowcount.max()) + 1


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
    use_sp = n >= SPARSE_CHOL_FROM and _have_cholmod()
    ab = np.zeros((1 if use_sp else bw + 1, n))
    E2, tr = Fr(0), Fr(0)
    for (a, b), v in exact.items():
        fv = float(v)
        if not use_sp:
            ab[a - b, b] = fv
        err = v - Fr(fv)
        E2 += err * err * (1 if a == b else 2)
        if a == b:
            tr += Fr(fv)
    Hs = "absent"
    if use_sp:
        ks = list(exact)
        Hs = _chol_sparse(n, np.array([a for a, b in ks]), np.array([b for a, b in ks]),
                          np.array([float(exact[k]) for k in ks]))
        if Hs is None:
            return None
    if Hs == "absent":
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
    H = min(n, bw + 1) + 1 if Hs == "absent" else min(n + 1, Hs)
    gH = H * u / (1 - H * u)
    g2 = 2 * u / (1 - 2 * u)
    g = (g2 + 2 * gH) / (1 - gH)
    lam = mu - g / (1 - g) * max(tr, Fr(0)) - _sqrt_up(E2)
    return lam if lam > 0 else None


def pd_ieee_float(n, rows, cols, vals, d2, mu):
    """pd_ieee for a matrix GIVEN IN FLOATS with a proved distance to the exact one (2026-11-02, ztl-stand's stability
    bisection built every step's matrix in exact fractions — 7.5 s a step on 36750 unknowns — only to have it rounded
    here). Input: the lower triangle (rows[i] >= cols[i]) of A0 in float64 (these numbers ARE A0), and d2 >= the
    squared Frobenius distance ||K - A0||_F^2 (both triangles) to the exact K the caller means. Then A_f = A0 - mu I
    with the diagonal rounded (its own errors bounded exactly here), ||E||_F <= sqrt(d2) + sqrt(sum of the diagonal
    roundings^2) (the triangle inequality), and the rest is pd_ieee's: lambda_min(K) >= mu - g/(1 - g) tr(A_f) - ||E||_F.
    Lean: ZRound `pd_lower` needs only sum E_ij^2 <= s^2 — s here is that bound. Returns the rational or None."""
    import numpy as np
    import scipy.sparse as sp
    from scipy.sparse.csgraph import reverse_cuthill_mckee
    from scipy.linalg import cholesky_banded, LinAlgError
    mu = _q(mu)
    rows, cols, vals = np.asarray(rows), np.asarray(cols), np.asarray(vals, dtype=float)
    if not np.all(np.isfinite(vals)):
        return None
    pat = sp.csr_matrix((np.ones(2 * len(rows)), (np.concatenate([rows, cols]), np.concatenate([cols, rows]))),
                        shape=(n, n))
    perm = reverse_cuthill_mckee(pat, symmetric_mode=True)
    inv = np.empty(n, dtype=np.int64)
    inv[perm] = np.arange(n)
    a, b = inv[rows], inv[cols]
    hi, lo = np.maximum(a, b), np.minimum(a, b)
    bw = int((hi - lo).max()) if len(hi) else 0
    if len(np.unique(hi * (n + 1) + lo)) != len(hi):
        raise ValueError("pd_ieee_float: duplicate entries — sum them first")
    use_sp = n >= SPARSE_CHOL_FROM and _have_cholmod()
    ab = np.zeros((1 if use_sp else bw + 1, n))
    off = hi != lo
    if not use_sp:
        ab[(hi - lo)[off], lo[off]] = vals[off]           # off-diagonal: exact floats, no new error
    diag0 = np.zeros(n)
    dmask = ~off
    diag0[hi[dmask]] = vals[dmask]
    E2d, tr = Fr(0), Fr(0)
    mf = float(mu)
    dv = diag0 - mf
    for d in range(n):                                    # the diagonal: exact a - mu, its rounding bounded exactly
        ex = Fr(float(diag0[d])) - mu
        fv = float(dv[d])
        err = ex - Fr(fv)
        E2d += err * err
        tr += Fr(fv)
        ab[0, d] = fv
    Hs = "absent"
    if use_sp:
        hs = np.concatenate([hi[off], np.arange(n)])
        ls = np.concatenate([lo[off], np.arange(n)])
        Hs = _chol_sparse(n, hs, ls, np.concatenate([vals[off], ab[0]]))
        if Hs is None:
            return None
    if Hs == "absent":
        try:
            cholesky_banded(ab, lower=True, overwrite_ab=True, check_finite=True)
        except (LinAlgError, ValueError):
            return None
    u = Fr(1, 2 ** 53)
    H = min(n, bw + 1) + 1 if Hs == "absent" else min(n + 1, Hs)
    gH = H * u / (1 - H * u)
    g2 = 2 * u / (1 - 2 * u)
    g = (g2 + 2 * gH) / (1 - gH)
    lam = mu - g / (1 - g) * max(tr, Fr(0)) - _sqrt_up(_q(d2)) - _sqrt_up(E2d)
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


def fp_prepare_K(parts, n, bits=192, pd="ieee", K=None, T=None):
    """The LOAD-INDEPENDENT half of _fp_prepare (2026-11-02, many load combinations in one run): the float factor
    and the proved lam_min(K0) — 70 % of a 7500-unknown frame's preparation (MEASURED: 5.1 of 7.4 s). Pass the result
    as `kctx` to _fp_prepare for every load case of the same structure."""
    import numpy as np
    import scipy.sparse.linalg as sla
    if K is None:
        T = _check_parts(parts)
        K = matrix(parts, n)
    A = _float_matrix(K, n)
    lu = sla.splu(A)
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
    return {"K": K, "T": T, "lu": lu, "lam": lam, "bits": used_bits, "parts_id": id(parts)}


def _fp_prepare(parts, f, n, bits=192, pd="ieee", K=None, T=None, kctx=None):
    """The floating path's SHARED work, done once for any number of outputs (2026-11-01): the float factor, a
    proved lam, u~ with its exact residual and energy, and every term's g.u~. K, T given (certify_general): the base
    matrix A0 and the proved theta instead of sum(parts) and max t. kctx (fp_prepare_K of the SAME parts / K):
    the factor and lam are reused — only the load's half is computed here."""
    import numpy as np
    if kctx is None:
        kctx = fp_prepare_K(parts, n, bits, pd, K, T)
    elif kctx.get("parts_id") != id(parts):
        raise ValueError("kctx was prepared for other parts")
    K, T, lu, lam, used_bits = kctx["K"], kctx["T"], kctx["lu"], kctx["lam"], kctx["bits"]
    uf = lu.solve(np.array([float(x) for x in f]))
    ut = [Fr(float(x)) for x in uf]                     # dyadic: exact, short
    Ku = _kmul(K, ut, n)
    ru = [_q(f[i]) - Ku[i] for i in range(n)]
    eu = _sqrt_up(sum(x * x for x in ru) / lam)          # ||u0 - u~||_K0
    nu_t = _sqrt_up(sum(a * b for a, b in zip(ut, Ku)))   # ||u~||_K0
    gu = [[_dot(g, ut) for _, g in p["terms"]] for p in parts]
    return {"T": T, "K": K, "lu": lu, "n": n, "lam": lam, "bits": used_bits, "ut": ut, "ru": ru, "eu": eu,
            "nu_t": nu_t, "nu": nu_t + eu, "gu": gu, "int": _int_tables(K, n, parts, gu, ru)}


def _lcm_den(xs):
    d = 1
    for x in xs:
        d = d * x.denominator // math.gcd(d, x.denominator)
    return d


def _int_tables(K, n, parts, gu, ru):
    """The same exact numbers as integers over shared denominators (2026-11-01, MEASURED: Fraction's gcd on every
    operation was the whole cost of an output — 0.5 s each on a 7500-unknown frame). Rows of K0 with one denominator
    per row; every part's c_P = sum_terms w (g.y)(g.u~) as (sum_terms qn (gi.Y)) / (qd 2^E); r_u over its own
    denominators. Nothing is rounded: _fp_output gives bit-identical results to _fp_output_ref (self-test)."""
    rows = [[] for _ in range(n)]
    for (i, j), v in K.items():
        rows[i].append((j, v))
        if i != j:
            rows[j].append((i, v))
    krows = []
    for r in rows:
        d = _lcm_den([v for _, v in r])
        krows.append((d, [(j, v.numerator * (d // v.denominator)) for j, v in r]))
    pt = []
    for p, gus in zip(parts, gu):
        ts, qs = [], []
        for (w, g), gv in zip(p["terms"], gus):
            gq = [(i, _q(c)) for i, c in g.items()]
            dg = _lcm_den([c for _, c in gq])
            ts.append([(i, c.numerator * (dg // c.denominator)) for i, c in gq])
            qs.append(_q(w) * gv / dg)
        qd = _lcm_den(qs)
        pt.append((qd, [(gi, q.numerator * (qd // q.denominator)) for gi, q in zip(ts, qs)]))
    return {"krows": krows, "parts": pt, "ru": [(x.numerator, x.denominator) for x in ru]}


def _grouped(pairs):
    """sum of num/den over (num, den) pairs, adding integers per denominator first."""
    acc = {}
    for a, d in pairs:
        if a:
            acc[d] = acc.get(d, 0) + a
    return sum((Fr(a, d) for d, a in acc.items()), Fr(0))


def _fp_output(ctx, parts, e, k=None):
    """One output on a prepared floating path (see certify_output_fp) — in integers over shared denominators;
    the same exact rationals as _fp_output_ref, bit for bit (self-test). With `k` (a part index) the slopes are not
    built; instead `D1p`, scaled_from's first order for part k, in O(1): D1 - t_k|c_k| + t_k|nominal - c_k|."""
    import numpy as np
    n, lam, T = ctx["n"], ctx["lam"], ctx["T"]
    ut, eu, nu_t, nu = ctx["ut"], ctx["eu"], ctx["nu_t"], ctx["nu"]
    it = ctx["int"]
    yf = ctx["lu"].solve(np.array([float(x) for x in e]))
    rat = [float(x).as_integer_ratio() for x in yf]
    E = max((d.bit_length() - 1 for _, d in rat), default=0)
    Y = [a << (E - (d.bit_length() - 1)) for a, d in rat]         # y~_i = Y_i / 2^E, exactly
    P2 = 1 << E
    KY = [sum(k * Y[j] for j, k in row) for _, row in it["krows"]]  # (K0 y~)_i = KY_i / (D_i 2^E)
    eq = [_q(x) for x in e]
    # r_y = e - K0 y~, |r_y|^2, y~.K0 y~ and the centre, grouped by denominator
    sq, cross = [], []
    for i, (D, _) in enumerate(it["krows"]):
        en, ed = eq[i].numerator, eq[i].denominator
        num = en * D * P2 - ed * KY[i]                            # r_y,i = num / (ed D 2^E)
        den = ed * D * P2
        sq.append((num * num, den * den))
        cross.append((Y[i] * KY[i], D))
    ey = _sqrt_up(_grouped(sq) / lam)
    ny_t = _sqrt_up(_grouped(cross) / (P2 * P2))
    ny = ny_t + ey
    centre = sum((x * ut[i] for i, x in enumerate(eq) if x), Fr(0)) + \
        _grouped((Y[i] * rn, rd) for i, (rn, rd) in enumerate(it["ru"])) / P2
    cerr = ey * eu
    signed, acc, ck = [], {}, None
    for P, (p, (qd, ts)) in enumerate(zip(parts, it["parts"])):
        cn = sum(q * sum(c * Y[i] for i, c in gi) for gi, q in ts)   # c_P = cn / (qd 2^E)
        if k is None:
            signed.append(Fr(cn, qd * P2))
        elif P == k:
            ck = Fr(cn, qd * P2)
        if cn:
            key = (qd, _q(p["t"]))
            acc[key] = acc.get(key, 0) + abs(cn)
    D1 = sum((t * Fr(a, qd) for (qd, t), a in acc.items()), Fr(0)) / P2
    D1raw = D1
    slope_err = T * (ey * nu + ny_t * eu)
    D1 += slope_err
    rest = T * T / (1 - T) * ny * nu if T else Fr(0)
    out = {"nominal": centre, "nominal_err": cerr, "slope_err": slope_err, "ey": ey, "ny_t": ny_t,
           "lo": centre - cerr - D1 - rest, "hi": centre + cerr + D1 + rest,
           "first": D1, "rest": rest, "T": T, "slopes": [-c for c in signed] if k is None else None, "lam": lam,
           "bits": ctx["bits"]}
    if k is not None:                                   # slope_k = -c_k; scaled_from adds the nominal to it
        tk = _q(parts[k]["t"])
        out["D1p"] = D1raw - tk * abs(ck) + tk * abs(centre - ck)
    return out


def _fp_outputs_batch(ctx, parts, es, ks):
    """MANY outputs of one prepared floating path at once (2026-11-02, the curator's "лечить"): the night battery's
    250x48 frame spent 40 min in 24250 one-at-a-time _fp_output calls (its stability proof needs every member's
    force) — each a Python pass over the whole system in big integers, ~N^2. Here a batch of outputs is solved with
    ONE matrix right-hand side and every per-output vector quantity is computed in IEEE floats, each with a
    RIGOROUS rounding bound added (Higham, Accuracy and Stability, 2nd ed., eq. 3.5: a computed sum of m products,
    ANY order, FMA allowed, errs by at most gamma_m times the sum of the absolute products; lean/ZHigham.lean
    `cholesky_entry_tree` is that statement for a summation tree). Same PREMISE as pd_ieee: IEEE 754 binary64,
    round to nearest. One gamma = gamma_N, N = n + the widest row/term/part + 64, covers every chain; every computed
    sum of nonnegative bounds is raised by (1 + 2 gamma) (S <= fl(S)/(1 - gamma)); a slack of N 2^-1000 absorbs
    underflow. The scalars of each output are then combined EXACTLY as in _fp_output; the centre is the float one
    (a dyadic), its rounding bound joins nominal_err, so an interval here CONTAINS the exact path's (self-test).
    ks[i] (a part index) as in _fp_output's k: D1p = (upper bound of the whole first-order sum) - (LOWER bound of
    part k's term) + (upper bound of t_k |centre - c_k|). Slopes are not returned (callers with `scale` only)."""
    import numpy as np
    import scipy.sparse as sp
    n, lam, T = ctx["n"], ctx["lam"], ctx["T"]
    eu, nu_t, nu = ctx["eu"], ctx["nu_t"], ctx["nu"]
    fb = ctx.get("_batch")
    if fb is None:
        rows, cols, vals = [], [], []
        for (i, j), v in ctx["K"].items():
            rows.append(i); cols.append(j); vals.append(float(v))
            if i != j:
                rows.append(j); cols.append(i); vals.append(float(v))
        A = sp.csr_matrix((vals, (rows, cols)), shape=(n, n))
        trow, tcol, tval, wgu, tpart = [], [], [], [], []
        widest = int(np.diff(A.indptr).max()) if n else 1
        for P, (p, gus) in enumerate(zip(parts, ctx["gu"])):
            widest = max(widest, len(p["terms"]))
            for (w, g), gv in zip(p["terms"], gus):
                t_ = len(wgu)
                for i, c in g.items():
                    trow.append(t_); tcol.append(i); tval.append(float(c))
                widest = max(widest, len(g))
                wgu.append(float(_q(w) * gv))
                tpart.append(P)
        nt = len(wgu)
        Gm = sp.csr_matrix((tval, (trow, tcol)), shape=(nt, n))
        Pm = sp.csr_matrix((np.ones(nt), (tpart, list(range(nt)))), shape=(len(parts), nt))
        N = n + widest + 64
        u = Fr(1, 2 ** 53)
        g_ = N * u / (1 - N * u)
        fb = {"A": A, "Aabs": abs(A), "Gm": Gm, "Gabs": abs(Gm), "Pm": Pm, "wgu": np.array(wgu),
              "awgu": np.abs(np.array(wgu)), "tP": np.array([float(_q(p["t"])) for p in parts]),
              "ut": np.array([float(x) for x in ctx["ut"]]), "ru": np.array([float(x) for x in ctx["ru"]]),
              "g": g_, "gf": float(g_) * 1.0000001, "up": 1 + 2 * g_, "slack": Fr(N, 2 ** 1000)}
        ctx["_batch"] = fb
    A, Aabs, g, gf, up, slack = fb["A"], fb["Aabs"], fb["g"], fb["gf"], fb["up"], fb["slack"]
    ut, ru = fb["ut"], fb["ru"]
    E = np.zeros((n, len(es)))                                          # n x b (each entry rounded: inside gamma)
    for col, e in enumerate(es):                                        # a sparse output {i: v} is read as given
        for i, x in (e.items() if isinstance(e, dict) else ((i, x) for i, x in enumerate(e) if x)):
            E[i, col] = float(x)
    Y = ctx["lu"].solve(E)                                             # y~: these floats ARE the trial vectors
    if Y.ndim == 1:
        Y = Y[:, None]
    KY, aKY = A @ Y, Aabs @ np.abs(Y)
    R = E - KY
    Rb = np.abs(R) + 2 * gf * (np.abs(E) + aKY)                        # |r_i| <= |fl r_i| + gamma(|e_i| + sum|K||y|)
    s_ey = (Rb * Rb).sum(axis=0)
    s_ny = (Y * KY).sum(axis=0)
    s_ny_abs = (np.abs(Y) * aKY).sum(axis=0)
    c_f = (E * ut[:, None]).sum(axis=0) + (Y * ru[:, None]).sum(axis=0)
    c_abs = (np.abs(E) * np.abs(ut)[:, None]).sum(axis=0) + (np.abs(Y) * np.abs(ru)[:, None]).sum(axis=0)
    Gy = fb["Gm"] @ Y
    C = fb["Pm"] @ (fb["wgu"][:, None] * Gy)                            # c_P (parts x b)
    Cerr = 3 * gf * (fb["Pm"] @ (fb["awgu"][:, None] * (fb["Gabs"] @ np.abs(Y))))
    D1s = (fb["tP"][:, None] * (np.abs(C) + Cerr)).sum(axis=0)
    out = []
    for i in range(Y.shape[1]):
        ey = _sqrt_up((Fr(float(s_ey[i])) * up + slack) / lam)
        ny_t = _sqrt_up(max(Fr(float(s_ny[i])) + 3 * g * Fr(float(s_ny_abs[i])) * up + slack, Fr(0)))
        ny = ny_t + ey
        centre = Fr(float(c_f[i]))
        c_err = 3 * g * Fr(float(c_abs[i])) * up + slack
        cerr = ey * eu + c_err
        D1raw = Fr(float(D1s[i])) * up * (1 + 2 * g) + slack            # the t_P rounding inside one more gamma
        slope_err = T * (ey * nu + ny_t * eu)
        D1 = D1raw + slope_err
        rest = T * T / (1 - T) * ny * nu if T else Fr(0)
        r = {"nominal": centre, "nominal_err": cerr, "slope_err": slope_err, "ey": ey, "ny_t": ny_t,
             "lo": centre - cerr - D1 - rest, "hi": centre + cerr + D1 + rest, "first": D1, "rest": rest, "T": T,
             "slopes": None, "lam": lam, "bits": ctx["bits"]}
        k = ks[i] if ks is not None else None
        if k is not None:
            tk = _q(parts[k]["t"])
            ck = Fr(float(C[k, i]))
            ce = Fr(float(Cerr[k, i])) * up + slack
            r["D1p"] = D1raw - tk * max(abs(ck) - ce, Fr(0)) + tk * (abs(centre - ck) + ce)
        out.append(r)
    return out


def _fp_output_ref(ctx, parts, e):
    """One output on a prepared floating path (see certify_output_fp) — the Fraction reference _fp_output must
    reproduce exactly."""
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
    return {"nominal": centre, "nominal_err": cerr, "slope_err": slope_err, "ey": ey, "ny_t": ny_t,
            "lo": centre - cerr - D1 - rest, "hi": centre + cerr + D1 + rest,
            "first": D1, "rest": rest, "T": T, "slopes": [-c for c in signed], "lam": lam, "bits": ctx["bits"]}


def certify_output_fp(parts, f, e, n, bits=192, pd="ieee"):
    """As certify_output, without exact solves: floats searched, everything CHECKED exactly (see above).
    Returns the same keys (lo, hi, nominal as an interval midpoint, first, rest, T, slopes) plus 'lam'."""
    return _fp_output(_fp_prepare(parts, f, n, bits, pd), parts, e)


_MANY = {}


def _finish(r, parts, scale, idx):
    """certify_many's per-output tail: scaled_from by part scale[idx] (when given), WITHOUT the per-part slopes —
    m outputs times m slopes was the whole cost on large systems (MEASURED 2026-11-01: 7500-unknown frame, 4900
    outputs, slopes pickled back and re-summed in the parent)."""
    if scale is None:
        return r
    sc = scaled_from(r, parts, scale[idx])
    return {"nominal": sc["nominal"], "lo": sc["lo"], "hi": sc["hi"], "unscaled": [r["lo"], r["hi"]]}


def _dense(e, n):
    if not isinstance(e, dict):
        return e
    out = [Fr(0)] * n
    for i, v in e.items():
        out[i] = _q(v)
    return out


def _cores():
    """The cores this process may use (~/bin/heavy --cores sets the affinity), at least 1."""
    import os
    try:
        return max(1, len(os.sched_getaffinity(0)))
    except AttributeError:
        return max(1, os.cpu_count() or 1)


def _batch_worker(ab):
    a, b = ab
    try:                                                # one BLAS thread per process: N processes x 32 threads thrash
        from threadpoolctl import threadpool_limits    # (MEASURED 2026-11-02: 100x24 frame 16 s serial -> 86 s)
        threadpool_limits(1)
    except ImportError:
        pass
    c = _MANY
    return _fp_outputs_batch(c["ctx"], c["parts"], c["es"][a:b], c["scale"][a:b])


def _many_worker(idx):
    c = _MANY
    k = None if c["scale"] is None else c["scale"][idx]
    return idx, _finish(_fp_output(c["ctx"], c["parts"], c["es"][idx], k), c["parts"], c["scale"], idx)


def certify_cases(parts, fs, es, n, jobs=1, exact_up_to=None, scale=None):
    """certify_many for SEVERAL LOAD CASES of one structure (2026-11-02): the outputs es (the same for every case)
    certified for every load vector in fs; on the floating path the factor and the proved lam_min(K0) are prepared
    ONCE (fp_prepare_K) and only each case's u~, residual and outputs are computed per case. Returns one list of
    results per case, each equal to certify_many(parts, f, es, n, ...) for that f."""
    lim = EXACT_UP_TO if exact_up_to is None else exact_up_to
    if n <= lim:
        return [certify_many(parts, f, es, n, jobs, exact_up_to, scale) for f in fs]
    kctx = fp_prepare_K(parts, n)
    return [certify_many(parts, f, es, n, jobs, exact_up_to, scale, kctx=kctx) for f in fs]


def certify_many(parts, f, es, n, jobs=1, exact_up_to=None, scale=None, kctx=None):
    """Many outputs of ONE system (2026-11-01): the shared work once — the exact path's LDL^T and u0, or the floating
    path's factor, proved lam and u~ — and each output's own work (its y, residual, first order) per output, in
    `jobs` processes on the floating path. Results equal certify's, output by output. With `scale` (a part index
    per output) each result is scaled_from(r, parts, scale[i])'s nominal/lo/hi instead, computed where r is and
    returned without slopes. An output may be a sparse dict {i: v} (2026-11-02: a 7500-unknown frame's 4900 dense
    outputs cost 36 M float(Fraction) calls of zeros); the batch reads it as is, every other path densifies it."""
    if scale is None or len(es) < BATCH_FROM or n <= (EXACT_UP_TO if exact_up_to is None else exact_up_to):
        es = [_dense(e, n) for e in es]
    if n <= (EXACT_UP_TO if exact_up_to is None else exact_up_to):
        rs = [certify_output(parts, f, e, n) for e in es] if len(es) <= 1 else _exact_many(parts, f, es, n)
        return [_finish(r, parts, scale, i) for i, r in enumerate(rs)]
    ctx = _fp_prepare(parts, f, n, kctx=kctx)
    if scale is not None and len(es) >= BATCH_FROM:     # the batch: floats with rigorous rounding bounds (2026-11-02)
        par = len(es) >= PARALLEL_FROM and _cores() > 1
        bs = 64 if par else BATCH                       # a worker holds ~12 n x bs float arrays: keep them small
        chunks = [(a, min(a + bs, len(es))) for a in range(0, len(es), bs)]
        # MEASURED 2026-11-02: 24 workers x 12 arrays of 36750 x 256 floats hit the 18 GB cap (killed); budget ~6 GB
        procs = min(len(chunks), _cores(), max(1, int(6e9 // (12 * 8 * n * bs)))) if par else 1
        if procs > 1:                                   # batches are independent: one process each (fork: ctx shared)
            import multiprocessing as mp
            _fp_outputs_batch(ctx, parts, es[:1], scale[:1])          # build the float tables once, before forking
            _MANY.clear()
            _MANY.update({"ctx": ctx, "parts": parts, "es": es, "scale": scale})
            pool = mp.get_context("fork").Pool(procs)
            try:
                got = pool.map(_batch_worker, chunks, chunksize=1)
                pool.close()                            # close + join: terminate() waited 17 s on a large result pipe
                pool.join()
            except BaseException:
                pool.terminate()
                raise
            _MANY.clear()
            rs = [r for part in got for r in part]
        else:
            rs = []
            for a, b in chunks:
                rs += _fp_outputs_batch(ctx, parts, es[a:b], scale[a:b])
        return [_finish(r, parts, scale, i) for i, r in enumerate(rs)]
    if jobs <= 1 or len(es) <= 1:
        return [_finish(_fp_output(ctx, parts, e, None if scale is None else scale[i]), parts, scale, i)
                for i, e in enumerate(es)]
    import multiprocessing as mp
    _MANY.clear()
    _MANY.update({"ctx": ctx, "parts": parts, "es": es, "scale": scale})
    with mp.get_context("fork").Pool(min(jobs, len(es))) as pool:
        out = dict(pool.map(_many_worker, range(len(es)), chunksize=max(1, len(es) // (8 * jobs))))
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
    if r.get("D1p") is not None:
        D1p = r["D1p"]                                  # computed with the output (_fp_output's k)
    else:
        D1p = Fr(0)
        for i, (p, sl) in enumerate(zip(parts, r["slopes"])):
            D1p += _q(p["t"]) * abs(sl + (centre if i == k else 0))
    half = cerr + D1p + serr + tk * cerr + tk * r["first"] + r["rest"] * (1 + tk)
    return {"nominal": centre, "lo": centre - half, "hi": centre + half, "base": r}


def prove_theta(A0, M, n, guess=None):
    """A proved theta < 1 with theta A0 - M positive definite (pd_ieee), M = sum r_i P_i + C — or None. The float
    estimate: the largest eigenvalue of M v = theta A0 v; then up by 1 %, 5 %, ... until the certificate holds."""
    import numpy as np
    import scipy.sparse.linalg as sla
    if not any(M.values()):
        return Fr(0)                                    # no perturbation at all: 0 <= 0 A0 exactly
    A = _float_matrix(A0, n)
    Mf = _float_matrix(M, n)
    try:
        th = float(sla.eigsh(Mf, k=1, M=A, which="LA", return_eigenvectors=False, v0=np.ones(n))[0])
    except Exception:
        th = guess or 0.5
    th = max(th, 1e-12)
    for grow in (Fr(101, 100), Fr(105, 100), Fr(115, 100), Fr(140, 100), Fr(2)):
        theta = Fr(th) * grow
        if theta >= 1:
            return None
        X = {key: theta * v for key, v in A0.items()}
        for key, v in M.items():
            X[key] = X.get(key, Fr(0)) - v
        try:
            mu = float(sla.eigsh(_float_matrix(X, n), k=1, sigma=0, which="LM", return_eigenvectors=False,
                                 v0=np.ones(n))[0])
        except Exception:
            continue
        if mu > 0 and pd_ieee(n, X, Fr(mu) * Fr(1, 2)) is not None:
            return theta
    return None


def certify_general(A0, parts, Cterms, f, e, n, theta=None):
    """THE SECOND-ORDER CASE (2026-11-01, ztl-stand frames, the curator's "(а)"): A(delta) = A0 + sum_i delta_i P_i - D,
    P_i = sum w g g^T PSD with |delta_i| <= r_i (part["t"] = r_i, any size), D unknown with 0 <= D <= C = sum Cterms.
    With M = sum r_i P_i + C <= theta A0 (theta proved, < 1), for every such A: e.u in [lo, hi],
        first order  sum_i r_i |y~' P_i u~| + slope error theta (e_y |u| + |y~| e_u) + (|y~|_C + sqrt(theta) e_y)
                     (|u~|_C + sqrt(theta) e_u)        (|y' D u| <= |y|_D |u|_D <= |y|_C |u|_C),
        rest         theta^2/(1 - theta) |y| |u|        (|x' Delta y| <= |x|_M |y|_M <= theta |x|_A0 |y|_A0),
    zenergy's own bound with T replaced by the proved theta and the D term added. A0 need not be a sum of the parts
    (here K0 + K_G(N_mid), indefinite pieces, positive definite in total)."""
    return certify_general_many(A0, parts, Cterms, f, [e], n, theta)[0]


def certify_general_many(A0, parts, Cterms, f, es, n, theta=None, cgroups=None):
    """certify_general for many outputs of one system: theta proved once, the factor and u~ once (2026-11-01).
    cgroups (2026-11-02): a list of term lists (pieces of C, e.g. one member's); each output then carries
    r["c_groups"] = [|y~|_G upper bounds] (y~ the output's floating adjoint, exactly) — a caller bounding a sum of
    LOCAL terms sum_g |y|_G r_g can use them with |y - y~|_C <= sqrt(theta) (ey + theta/(1 - theta) |y0|_A0)."""
    for p in parts:
        if _q(p["t"]) < 0 or any(_q(w) < 0 for w, _ in p["terms"]):
            raise ValueError("a part's radius or a term's weight is negative")
    M = matrix([{"t": 0, "terms": [(_q(p["t"]) * _q(w), g) for w, g in p["terms"]]} for p in parts]
               + [{"t": 0, "terms": list(Cterms)}], n)
    if theta is None:
        theta = prove_theta(A0, M, n)
    if theta is None:
        raise ArithmeticError("theta < 1 not proved: the perturbations are not small against A0")
    ctx = _fp_prepare(parts, f, n, K=A0, T=theta)
    import numpy as np
    cn = lambda v: _sqrt_up(sum(_q(w) * _dot(g, v) ** 2 for w, g in Cterms)) if Cterms else Fr(0)
    st = _sqrt_up(theta)
    cu = cn(ctx["ut"]) + st * ctx["eu"]
    out = []
    for e in es:
        r = _fp_output(ctx, parts, e)
        yt = [Fr(float(x)) for x in ctx["lu"].solve(np.array([float(x) for x in e]))]
        extra = (cn(yt) + st * r["ey"]) * cu if Cterms else Fr(0)
        if cgroups is not None:
            r["c_groups"] = [_sqrt_up(sum(_q(w) * _dot(g, yt) ** 2 for w, g in grp)) for grp in cgroups]
        r["lo"] -= extra
        r["hi"] += extra
        r["first"] += extra
        r["theta"] = theta
        r["d_term"] = extra
        out.append(r)
    return out


def enclose_linear(parts, f, n, As, exact_up_to=None):
    """[lo, hi] containing a.u0 (u0 = K0^-1 f, the NOMINAL solution) for every sparse functional a = {i: v} in As,
    from ONE solve (2026-11-01, for ztl-stand's proved upper bound on the critical load factor). Exact path: u0
    solved exactly, residual checked, radius 0. Floating path: u~ in dyadics, exact residual r = f - K0 u~,
    ||u0 - u~||_K0 <= eu = sqrt(|r|^2 / lam) (lam <= lambda_min(K0) proved by pd_ieee), and
    |a.(u0 - u~)| <= ||a||_K0^-1 eu <= sqrt(|a|^2 / lam) eu (Cauchy-Schwarz in the K0 inner product)."""
    lim = EXACT_UP_TO if exact_up_to is None else exact_up_to
    if n <= lim:
        K = matrix(parts, n)
        L, d = ldl(n, K)
        u = solve(L, d, f)
        _check_solution(K, u, f)
        out = []
        for a in As:
            v = sum(_q(c) * u[i] for i, c in a.items())
            out.append((v, v))
        return out
    ctx = _fp_prepare(parts, f, n)
    ut, eu, lam = ctx["ut"], ctx["eu"], ctx["lam"]
    out = []
    for a in As:
        v = sum(_q(c) * ut[i] for i, c in a.items())
        rad = _sqrt_up(sum(_q(c) * _q(c) for c in a.values()) / lam) * eu
        out.append((v - rad, v + rad))
    return out


def value_enclosure_fp(parts, f, e, n, ps, bits=192):
    """[lo, hi] containing e^T u at the point p (the floating path at that point: every part fixed, t = 0)."""
    scaled = [{"t": 0, "terms": [(_q(w) * _q(pi), g) for w, g in p["terms"]]} for p, pi in zip(parts, ps)]
    r = certify_output_fp(scaled, f, e, n, bits)
    return r["lo"], r["hi"]


# Exact solves up to this many unknowns, the floating path above. MEASURED 2026-11-01: the floating path gives the
# same widths to 4 digits and is faster from ~100 unknowns (plate 448: 0.05 s vs 28.6 s exact; frame 450: 0.03 s vs
# 4.2 s); it was 600 until the plates showed exact fractions growing faster than on frames (576 unknowns: 71 s).
EXACT_UP_TO = 120
# certify_many's batch (scaled outputs): from this many outputs, this many per matrix right-hand side
BATCH_FROM, BATCH = 32, 256
# ... and from this many outputs the batches run in parallel processes (below it a pool costs more than it saves,
# and the stand's own 24-shard test runs must not fan out 24 x 24)
PARALLEL_FROM = 2000


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
    el_n = 0
    for trial in range(10):                             # enclose_linear: the floating enclosure holds the exact value
        n, m = rng.randint(3, 8), rng.randint(2, 6)
        parts, f, _ = _random_case(rng, n, m, Fr(1, 100))
        As = [{i: Fr(rng.randint(-5, 5), rng.randint(1, 4)) for i in range(n) if rng.random() < 0.6} for _ in range(4)]
        ex = enclose_linear(parts, f, n, As)
        fp = enclose_linear(parts, f, n, As, exact_up_to=0)
        for (v, w), (lo, hi) in zip(ex, fp):
            assert v == w and lo <= v <= hi, (trial, v, lo, hi)
            el_n += 1
    print(f"   enclose_linear: {el_n} functionals, the floating enclosure contains the exact value every time")
    import itertools
    g_cases = g_pts = g_esc_rest = g_esc_d = g_cg = 0
    for trial in range(40):                             # certify_general: second-order systems, D in [0, C]
        n = rng.randint(3, 6)
        def rpart(m):
            out = []
            for _ in range(m):
                idx = rng.sample(range(n), rng.randint(1, min(3, n)))
                out.append((Fr(rng.randint(1, 9), rng.randint(1, 4)), {i: Fr(rng.randint(-3, 3) or 1) for i in idx}))
            return out
        Kp = [rpart(2) for _ in range(rng.randint(2, 4))]
        Gp = [rpart(1) for _ in range(rng.randint(1, 3))]
        A0 = matrix([{"t": 0, "terms": t} for t in Kp], n)
        for t_ in Gp:
            n0 = Fr(-rng.randint(0, 3), 10)
            for key, v in matrix([{"t": 0, "terms": t_}], n).items():
                A0[key] = A0.get(key, Fr(0)) + n0 * v
        parts = [{"t": Fr(rng.choice([1, 3, 5]), 100), "terms": t} for t in Kp] + \
                [{"t": Fr(rng.randint(0, 3), 100), "terms": t} for t in Gp]
        Ct = [(w / 50, g) for w, g in rpart(1)]
        f = [Fr(rng.randint(-5, 5)) for _ in range(n)]
        e = [Fr(rng.randint(-3, 3)) for _ in range(n)]
        try:
            r = certify_general(A0, parts, Ct, f, e, n)
        except ArithmeticError:
            continue
        g_cases += 1
        # c_groups (2026-11-02): |y|_G <= c_G + sqrt(theta) (e_y + theta/(1 - theta) |y0|_A0) for the EXACT y = A^-1 e
        # of every A below, each piece G of C — the bound ztl-stand's frames use for the member loads
        grp = [Ct[:len(Ct) // 2], Ct[len(Ct) // 2:]]
        rg = certify_general_many(A0, parts, Ct, f, [e], n, cgroups=grp)[0]
        th_ = rg["theta"]
        slack_ = _sqrt_up(th_) * (rg["ey"] + th_ / (1 - th_) * (rg["ny_t"] + rg["ey"]))
        Cm = matrix([{"t": 0, "terms": Ct}], n)
        Pm = [matrix([{"t": 0, "terms": p["terms"]}], n) for p in parts]
        pts = [([s_ * p["t"] for s_, p in zip(sg, parts)], df) for sg in itertools.islice(
            itertools.product((-1, 1), repeat=len(parts)), 32) for df in (Fr(0), Fr(1))]
        pts += [([p["t"] * Fr(rng.randint(-100, 100), 100) for p in parts], Fr(rng.randint(0, 100), 100))
                for _ in range(10)]
        for ds, df in pts:
            A = dict(A0)
            for d, P in zip(ds, Pm):
                for key, v in P.items():
                    A[key] = A.get(key, Fr(0)) + d * v
            for key, v in Cm.items():
                A[key] = A.get(key, Fr(0)) - df * v
            L, dd = ldl(n, A)
            val = sum(a * b for a, b in zip(e, solve(L, dd, f)))
            assert r["lo"] <= val <= r["hi"], (trial, val)
            y_ = solve(L, dd, e)
            for G_, c_ in zip(grp, rg["c_groups"]):
                assert sum(_q(w) * _dot(g, y_) ** 2 for w, g in G_) <= (c_ + slack_) ** 2, (trial, "c_groups")
                g_cg += 1
            g_pts += 1
            if not (r["lo"] + r["rest"] + r["d_term"] <= val <= r["hi"] - r["rest"] - r["d_term"]):
                g_esc_rest += 1
            if not (r["lo"] + r["d_term"] <= val <= r["hi"] - r["d_term"]):
                g_esc_d += 1
    assert g_cases >= 5 and g_esc_rest > 0 and g_esc_d > 0 and g_cg > 0, (g_cases, g_esc_rest, g_esc_d, g_cg)
    print(f"   certify_general (second order, D in [0, C]): {g_cases} systems, {g_pts} points inside [lo, hi]; "
          f"dropping the rest and the D term lets {g_esc_rest} escape, the D term alone {g_esc_d} (both needed); "
          f"c_groups: {g_cg} piece norms of the exact adjoint inside their bound")
    ii = 0
    for trial in range(20):                             # integer outputs == the Fraction reference, bit for bit
        n, m = rng.randint(3, 9), rng.randint(2, 7)
        parts, f, _ = _random_case(rng, n, m, Fr(rng.choice([1, 5, 20]), 100))
        ctx = _fp_prepare(parts, f, n)
        for k in range(m):
            e = [Fr(rng.randint(-4, 4), rng.randint(1, 3)) for _ in range(n)]
            full = _fp_output(ctx, parts, e)
            assert full == _fp_output_ref(ctx, parts, e), trial
            a, b = scaled_from(full, parts, k), scaled_from(_fp_output(ctx, parts, e, k), parts, k)
            assert (a["lo"], a["hi"], a["nominal"]) == (b["lo"], b["hi"], b["nominal"]), trial
            ii += 1
    print(f"   integer path: {ii} outputs bit-identical to the Fraction reference; O(1) scaled first order == "
          f"scaled_from over all slopes")
    # the BATCH (floats + rigorous rounding bounds) CONTAINS the exact path's scaled interval, within 1e-9 of it;
    # with the rounding bounds switched off it must stop containing it somewhere (the bounds are load-bearing)
    bb, worst, esc = 0, Fr(0), 0
    for trial in range(25):
        n, m = rng.randint(3, 12), rng.randint(2, 8)
        parts, f, _ = _random_case(rng, n, m, Fr(rng.choice([1, 5, 20]), 100))
        ctx = _fp_prepare(parts, f, n)
        es = [[Fr(rng.randint(-4, 4), rng.randint(1, 3)) for _ in range(n)] for _ in range(m)]
        ks = list(range(m))
        bat = _fp_outputs_batch(ctx, parts, es, ks)
        for e, k, rb in zip(es, ks, bat):
            a, b = scaled_from(_fp_output(ctx, parts, e, k), parts, k), scaled_from(rb, parts, k)
            assert b["lo"] <= a["lo"] and a["hi"] <= b["hi"], (trial, k)
            assert a["hi"] - a["lo"] >= 0
            worst = max(worst, ((b["hi"] - b["lo"]) - (a["hi"] - a["lo"])) / (abs(a["hi"]) + abs(a["lo"]) + 1))
            bb += 1
        ctx2 = dict(ctx)
        ctx2.pop("_batch", None)
        _fp_prepare_batch_mut = _fp_outputs_batch(ctx2, parts, es, ks)   # warm the cache, then switch bounds off
        ctx2["_batch"] = dict(ctx2["_batch"], g=Fr(0), gf=0.0, up=Fr(1), slack=Fr(0))
        for e, k, rb in zip(es, ks, _fp_outputs_batch(ctx2, parts, es, ks)):
            a, b = scaled_from(_fp_output(ctx, parts, e, k), parts, k), scaled_from(rb, parts, k)
            if b["lo"] > a["lo"] or a["hi"] > b["hi"]:
                esc += 1
    assert worst < Fr(1, 10 ** 9) and esc > 0, (worst, esc)
    print(f"   batch path: {bb} scaled outputs, each CONTAINS the exact interval (widened by <= {float(worst):.1e} "
          f"relative); rounding bounds off: {esc} stop containing it (the bounds are load-bearing)")
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
    # pd_ieee_float (a float matrix + its proved distance) agrees with pd_ieee on the exact matrix (2026-11-02)
    fl_ok = 0
    for trial in range(30):
        nn = rng.randint(3, 25)
        Km = {}
        for i in range(nn):
            Km[(i, i)] = Fr(rng.randint(20, 60))
            for j in range(i):
                if rng.random() < 0.3:
                    Km[(i, j)] = Fr(rng.randint(-9, 9), rng.randint(1, 7))
        mu_ = Fr(rng.randint(1, 30))
        a_ = pd_ieee(nn, Km, mu_)
        kk_ = list(Km)
        d2_ = sum((Km[k_] - Fr(float(Km[k_]))) ** 2 * (1 if k_[0] == k_[1] else 2) for k_ in kk_)
        b_ = pd_ieee_float(nn, [i for i, _ in kk_], [j for _, j in kk_], [float(Km[k_]) for k_ in kk_], d2_, mu_)
        assert (a_ is None) == (b_ is None) and (a_ is None or abs(a_ - b_) <= mu_ / 10 ** 9), (trial, a_, b_)
        fl_ok += 1
    print(f"   pd_ieee_float: {fl_ok} random matrices, the same verdict and bound as pd_ieee on the exact matrix")
    # the SPARSE Cholesky (CHOLMOD supernodal, 2026-11-02): the same verdicts as the banded one, both ways, and a
    # bound within a hair (H differs: the band vs the factor's longest row); a matrix with a negative eigenvalue refused
    global SPARSE_CHOL_FROM
    if _have_cholmod():
        keep_, sp_ok = SPARSE_CHOL_FROM, 0
        for trial in range(30):
            nn = rng.randint(5, 40)
            Km = {}
            for i in range(nn):
                Km[(i, i)] = Fr(rng.randint(20, 60))
                for j in range(i):
                    if rng.random() < 0.3:
                        Km[(i, j)] = Fr(rng.randint(-9, 9), rng.randint(1, 7))
            for mu_ in (Fr(rng.randint(1, 30)), Fr(200)):          # 200: above every diagonal -> not PD
                kk_ = list(Km)
                args = (nn, [i for i, _ in kk_], [j for _, j in kk_], [float(Km[k_]) for k_ in kk_],
                        sum((Km[k_] - Fr(float(Km[k_]))) ** 2 * (1 if k_[0] == k_[1] else 2) for k_ in kk_), mu_)
                SPARSE_CHOL_FROM = 10 ** 9
                a_, af_ = pd_ieee(nn, Km, mu_), pd_ieee_float(*args)
                SPARSE_CHOL_FROM = 1
                b_, bf_ = pd_ieee(nn, Km, mu_), pd_ieee_float(*args)
                SPARSE_CHOL_FROM = keep_
                assert (a_ is None) == (b_ is None) and (af_ is None) == (bf_ is None), (trial, a_, b_, af_, bf_)
                assert a_ is None or abs(a_ - b_) <= mu_ / 10 ** 9, (trial, a_, b_)
                assert mu_ != 200 or (b_ is None and bf_ is None), (trial, "not PD accepted")
                sp_ok += 1
        print(f"   sparse Cholesky (CHOLMOD supernodal): {sp_ok} cases, the banded verdicts and bounds; not-PD refused")
    else:
        print("   sparse Cholesky: CHOLMOD (scikit-sparse) not installed — the banded path only")
    # certify_cases (one factor and one proved lam for every load case) == certify_many case by case
    parts, f, e, n = _cantilever_demo(40)
    fs = [f, [x * 2 for x in f], [Fr(0)] * (n - 1) + [Fr(1)]]
    es_ = [e, [Fr(1)] + [Fr(0)] * (n - 1)]
    a_ = certify_cases(parts, fs, es_, n)
    b_ = [certify_many(parts, ff, es_, n) for ff in fs]
    assert all((x["lo"], x["hi"]) == (y["lo"], y["hi"]) for ra, rb in zip(a_, b_) for x, y in zip(ra, rb))
    print(f"   certify_cases: {len(fs)} load cases x {len(es_)} outputs, equal to certify_many case by case "
          f"(one factor, one proved lam)")
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
