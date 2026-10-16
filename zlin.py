"""LINEAR SYSTEMS OF ANY SIZE: a bound on one unknown of A(p) x = b(p) over a box of p, CHECKED EXACTLY (a kernel module).

The kernel's rules (exact arithmetic, no search, no budget, the cost follows the certificate), beside zcertify.py:
zcertify.check_system solves a system symbolically by Cramer's rule — n! terms, refused above MAX_SYSTEM = 6; this
module checks a CERTIFICATE over the box instead, for any size (2026-10-15). The search that builds the certificates
lives outside, as for zcertify; test_zlin.py carries a small one.

THE CLASS. n linear laws in n unknowns x; each coefficient of A and b is an expression (ZTL's reader nodes) of boxed
quantities p — resistors, gains, conductances, each anywhere in its own box. A square system, linear in x; nothing
else is assumed (no symmetry, no sign pattern).

WHAT IS CERTIFIED: max over the box of x_k <= U (or min >= L), x(p) the solution of A(p) x = b(p).

THE CERTIFICATE (brought by a search outside; trusted for nothing) is a tree over the box:
    {"split": name, "at": "p/q", "lo": tree, "hi": tree}      the piece cut at name = at
    {"leaf": "enclose", "R": [[...]], "x": [...]}              the enclosure on the piece settles the bound
    {"leaf": "pin", "signs": {name: "+"|"-"}, "R": [[...]], "x": [...], "then": tree}
    {"leaf": "exact"}                                          on a POINT (every name pinned): x_k solved exactly
    {"vertex": name, "R": [[...]], "x": [...], "lo": tree, "hi": tree}
                                                              name enters by one layer (step 6): the faces
                                                              name = lo and name = hi, each by its subtree
    (an enclose or pin leaf may carry "iter": m — m rounds of the componentwise refinement, step 4b;
     the root may be {"grid": bits, "tree": tree} — the fixed-point grid 2^-bits, 64..1024, default 64)
                                                              x_k is monotone in each listed name over the piece;
                                                              each is pinned at its unfavourable end and `then`
                                                              is checked on that smaller piece
R (an approximate inverse of A at some point) and x (an approximate solution) are fractions; any values are accepted —
a bad R or x only makes the check fail.

WHAT THE KERNEL DOES on a piece, exactly:
  1. [A], [b]: each coefficient's interval over the piece (ZTL's own reading: zcertify._reading);
  2. C = I - R [A] (an interval matrix) and beta = max_i sum_j |C_ij|; it must be < 1;
  3. z = R ([b] - [A] x), delta = max_i |z_i| / (1 - beta);
  2p. (and) the PARAMETRIC form of C and z: the same quantities read per boxed quantity through its derivative
     (mean value theorem), so a quantity that moves several coefficients is read once — C and z are the MEET of both
     forms (each encloses);
  4. every x in the solution set: x = x~ + e with e = R (b - A x~) + (I - R A) e, so |e|_inf <= delta, and
        x_i in  x~_i + z_i + [-1, 1] * (sum_j |C_ij|) * delta;
  4c. componentwise by a verified vector: any u >= |z| + |C| u bounds |e| <= u (rho(|C|) <= beta < 1); u is a
     float candidate checked exactly here; and for the signs ONE y with y^T (I - |C|) >= e_k^T |C| bounds
     |(C d)_k| <= y^T |zd| for every tolerance at once (step 5b);
  4b. (iter m) m rounds of E <- (z + C E) ∩ E, componentwise: the true e satisfies e = z + C e, so it stays in E —
     the norm bound of 4 drowns a far, weak component in the strongest one, the rounds give each its own width;
  5. (pin) d = dx/dp_j solves A d = -(dA/dp_j x - db/dp_j): with [r] = [dA/dp_j][x] - [db/dp_j] (the derivatives
     built by the kernel itself, zcertify.derivative; [x] from step 4) the same rule encloses d with z = -R[r]; the
     listed sign must hold on all of d_k's interval. Then x_k is monotone in p_j on the whole piece, so its extreme
     over the piece equals its extreme over the piece with p_j at the end the sign points to.
beta < 1 also proves every A in [A] nonsingular (R A = I - C is), so the system has one solution at every point.
The answer is (True, pieces) or (False, the first reason) — deterministic, never "not computed".

Prior art (operationalism, not novelty): the enclosure is the classical verified-solution theorem for interval linear
systems (Krawczyk 1969, Rump 1983, Neumaier 1990 "Interval Methods for Systems of Equations"); parametric systems and
monotonicity by derivative signs — Popova, Kolev, Skalna. What is ours: the certificate form and its exact check.
"""
from __future__ import annotations

import itertools
import os
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import zcertify as ZC                                   # noqa: E402
from znumjudge import _parse_arith                      # noqa: E402

ZERO = F(0)


class LinError(ValueError):
    pass


# ── fixed-point interval arithmetic (2026-10-15) ───────────────────────────────────────────────────────────────
# Every interval is a pair of INTEGERS, the value times G = 2^64, its lower end rounded down and its upper end up: an
# enclosure only widens, so it stays sound. R and x~ are rounded to the same grid by the kernel ITSELF — the theorem
# holds for ANY R and x~, so the kernel may use its own rounded ones, as long as it uses them throughout. (Python
# fractions grew their denominators every round of the refinement; integers keep the cost flat.)

G = 1 << 64            # the grid of THIS check: 2^-bits, bits from the certificate's root ("grid", 64..1024) — a
GRID = G               # system whose values are tiny (a long ladder: u ~ 1e-35) needs a finer grid than 2^-64
MIN_BITS, MAX_BITS = 64, 1024


class grid:
    """with grid(bits): every integer interval inside is on 2^-bits (the search uses it too)."""
    def __init__(self, bits):
        if not isinstance(bits, int) or not MIN_BITS <= bits <= MAX_BITS:
            raise LinError(f"grid must be an integer number of bits in {MIN_BITS}..{MAX_BITS}")
        self.bits = bits

    def __enter__(self):
        global G
        self.was, G = G, 1 << self.bits
        return self

    def __exit__(self, *exc):
        global G
        G = self.was


def _dn(v, s=None):
    return v // (G if s is None else s)


def _up(v, s=None):
    return -((-v) // (G if s is None else s))


def _ivi(iv):
    """A Fraction interval -> integers on the grid, outward."""
    lo, hi = iv
    return (_dn(lo.numerator * G, lo.denominator), _up(hi.numerator * G, hi.denominator))


def _rnd(v):
    return round(v * G)


def _smul(s, a):
    """scalar s (G) times interval a (G) -> G^2."""
    return (s * a[0], s * a[1]) if s >= 0 else (s * a[1], s * a[0])


def _imul(a, b):
    ps = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return (min(ps), max(ps))


def _mag(a):
    return max(abs(a[0]), abs(a[1]))


def _fiv(a):
    return (F(a[0], G), F(a[1], G))


def _out(a):
    """A Fraction interval rounded outward to the grid (kept for callers that round fractions)."""
    lo, hi = _ivi(a)
    return (F(lo, G), F(hi, G))


# ── the system ─────────────────────────────────────────────────────────────────────────────────────────────────

def system(laws, unknowns, qs):
    """laws ("lhs == rhs") -> (A, b) as reader nodes: A[i][j] the coefficient of unknowns[j] in law i, b[i] its
    right-hand side (A x = b). Raises LinError when a law is not linear in the unknowns or the system not square."""
    unknowns = list(unknowns)
    us = set(unknowns)
    rows = []
    for law in laws:
        if law.count("==") != 1:
            raise LinError(f"not one equality: {law!r}")
        l, r = law.split("==")
        try:
            a = ZC._lin(_parse_arith(l, qs), us)
            c = ZC._lin(_parse_arith(r, qs), us)
        except ZC.SystemError_ as e:
            raise LinError(str(e))
        row = dict(a)
        for k, v in c.items():
            row[k] = ("sub", row[k], v) if k in row else ("sub", ZERO, v)
        rows.append(row)
    if len(rows) != len(unknowns):
        raise LinError(f"{len(rows)} equalities for {len(unknowns)} unknowns: not a square system")
    A = [[row.get(u, ZERO) for u in unknowns] for row in rows]
    b = [("sub", ZERO, row[1]) if 1 in row else ZERO for row in rows]
    return A, b


def _read(node, qs, piece):
    """The node's interval over the piece (ZTL's reading), or LinError."""
    if isinstance(node, F):
        return (node, node)
    iv = ZC._reading(node, qs, piece)
    if iv is None:
        raise LinError(f"no interval reading of a coefficient over the piece")
    return iv


def _imatrix(A, qs, piece):
    return [[_read(e, qs, piece) for e in row] for row in A]


def _refine(z, C, E, iters):
    """Step 4b: e = z + C e holds for the true error, so e in E gives e in (z + C E) ∩ E — componentwise, sound at
    every iteration (Krawczyk's operator); `iters` from the certificate (the cost follows it). Integers on the grid."""
    n = len(z)
    for _ in range(iters):
        new = []
        for i in range(n):
            lo2, hi2 = z[i][0] * G, z[i][1] * G
            Ci = C[i]
            for j in range(n):
                c = Ci[j]
                if c[0] or c[1]:
                    p = _imul(c, E[j])
                    lo2 += p[0]
                    hi2 += p[1]
            lo, hi = max(_dn(lo2), E[i][0]), min(_up(hi2), E[i][1])
            if lo > hi:
                raise LinError("the refinement emptied an enclosure: the system has no solution there")
            new.append((lo, hi))
        if new == E:
            break
        E = new
    return E


def _param(A, b, qs, piece):
    """THE PARAMETRIC FORM (step 2p, 2026-10-15): A(p) = A(p0) + sum_j (p_j - p0_j) dA/dp_j(xi), xi on the segment from
    the piece's centre p0 (the mean value theorem, per coefficient), so over the piece A(p) - A(p0) lies in
    sum_j [-w_j, w_j] [dA/dp_j](piece), w_j the half-width — and the same for b. The interval matrix [A] forgets that
    two coefficients move with ONE quantity (a long ladder: x_19's enclosure 13x wider than its true range); here each
    quantity's whole effect is read together. -> {"A0", "b0", "terms": [(w_j, {(i, j): iv}, {i: iv})]} or None when a
    coefficient has no derivative (min/max): then only the interval form is used."""
    n = len(A)
    wide = {nm: (lo, hi) for nm, (lo, hi) in piece.items() if lo != hi}
    p0 = {nm: ((lo + hi) / 2, (lo + hi) / 2) for nm, (lo, hi) in piece.items()}
    A0 = [[_read(e, qs, p0) for e in row] for row in A]
    b0 = [_read(e, qs, p0) for e in b]
    names_of = {}
    for i in range(n):
        for j in range(n):
            if not isinstance(A[i][j], F):
                names_of[(i, j)] = ZC._names(A[i][j])
        if not isinstance(b[i], F):
            names_of[(i, None)] = ZC._names(b[i])
    terms = []
    try:
        for nm, (lo, hi) in wide.items():
            dA, db = {}, {}
            for (i, j), ns in names_of.items():
                if nm in ns:
                    e = A[i][j] if j is not None else b[i]
                    iv = _read(ZC.derivative(e, nm), qs, piece)
                    if iv != (0, 0):
                        (dA.__setitem__((i, j), iv) if j is not None else db.__setitem__(i, iv))
            if dA or db:
                terms.append((nm, (hi - lo) / 2, dA, db))
    except ZC.NoDerivative:
        return None
    return {"A0": A0, "b0": b0, "terms": terms}


def _meet(a, b):
    lo, hi = max(a[0], b[0]), min(a[1], b[1])
    if lo > hi:
        raise LinError("two enclosures of one quantity do not meet: a reading is wrong")
    return (lo, hi)


def _cols(M):
    """The non-zero entries of a matrix of integer intervals, by column: {j: [(m, iv)]}."""
    out = {}
    for m, row in enumerate(M):
        for j, a in enumerate(row):
            if a[0] or a[1]:
                out.setdefault(j, []).append((m, a))
    return out


def _rows_nz(M):
    return [[(j, a) for j, a in enumerate(row) if a[0] or a[1]] for row in M]


def _RtimesCols(Rr, cols, n, one):
    """C = one*I - R M for M given by its non-zero columns: {(i, j): (lo, hi)} in G^2, only where R M or I is non-zero
    (R is dense, so every column with an entry gives a full column of C)."""
    C = [[(0, 0)] * n for _ in range(n)]
    for i in range(n):
        Ri = Rr[i]
        Ci = C[i]
        for j, ent in cols.items():
            lo2 = hi2 = 0
            for m, a in ent:
                s_ = Ri[m]
                if s_:
                    if s_ >= 0:
                        lo2 += s_ * a[0]
                        hi2 += s_ * a[1]
                    else:
                        lo2 += s_ * a[1]
                        hi2 += s_ * a[0]
            Ci[j] = (-hi2, -lo2)
        if one:
            c = Ci[i]
            Ci[i] = (c[0] + one, c[1] + one)
    return C


def _residual(Brow, Anz, xr):
    """b - A x~ per row, G^2 -> G (outward); Anz the rows' non-zero entries."""
    out = []
    for m, row in enumerate(Anz):
        lo2, hi2 = Brow[m][0] * G, Brow[m][1] * G
        for j, a in row:
            x = xr[j]
            if x:
                if x >= 0:
                    lo2 -= x * a[1]
                    hi2 -= x * a[0]
                else:
                    lo2 -= x * a[0]
                    hi2 -= x * a[1]
        out.append((_dn(lo2), _up(hi2)))
    return out


def _Rtimes(Rr, v, n, sign=1):
    """sign * R v for an interval vector v given sparsely {m: iv} (G) -> [(lo, hi)] in G^2."""
    out = []
    for i in range(n):
        Ri = Rr[i]
        lo2 = hi2 = 0
        for m, t in v.items():
            s_ = Ri[m] * sign
            if s_:
                if s_ >= 0:
                    lo2 += s_ * t[0]
                    hi2 += s_ * t[1]
                else:
                    lo2 += s_ * t[1]
                    hi2 += s_ * t[0]
        out.append((lo2, hi2))
    return out


def _contract(Ai, R, par=None):
    """Step 2 alone — C = I - R [A] (the meet of the interval and the parametric form), its row sums and beta — with
    what step 3 reuses. C depends on A, R and the parametric terms' dA, NEVER on the right-hand side: the sign proofs
    of step 6 solve one system per quantity with the same A (and one with A^T), so a piece computes each C once
    (Muhanna's truss benchmark 1, 420 quantities: 840 recomputations of a 230 x 230 C per piece, 2026-10-16)."""
    n = len(Ai)
    AI = [[_ivi(a) for a in row] for row in Ai]
    Rr = [[_rnd(v) for v in row] for row in R]
    GG = G * G
    C2 = _RtimesCols(Rr, _cols(AI), n, GG)
    A0 = None
    if par is not None:
        A0 = [[_ivi(a) for a in row] for row in par["A0"]]
        Cp = [[list(c) for c in row] for row in _RtimesCols(Rr, _cols(A0), n, GG)]
        for _nm, w, dA, _db in par["terms"]:
            cols = {}
            for (m, j), iv in dA.items():
                cols.setdefault(j, []).append((m, _ivi(iv)))
            for j, ent in cols.items():
                for i in range(n):
                    Ri = Rr[i]
                    lo2 = hi2 = 0
                    for m, a in ent:
                        s_ = Ri[m]
                        if s_:
                            p_ = _smul(s_, a)
                            lo2 += p_[0]
                            hi2 += p_[1]
                    if lo2 or hi2:
                        rad = _up(max(abs(lo2), abs(hi2)) * w.numerator, w.denominator)
                        Cp[i][j][0] -= rad
                        Cp[i][j][1] += rad
        C = [[_meet((_dn(a[0]), _up(a[1])), (_dn(c[0]), _up(c[1]))) for a, c in zip(r2, rp)] for r2, rp in zip(C2, Cp)]
    else:
        C = [[(_dn(a[0]), _up(a[1])) for a in row] for row in C2]
    rows = [sum(_mag(c) for c in row) for row in C]
    beta = max(rows)
    if beta >= G:
        raise LinError(f"beta = {beta / G:.4g} >= 1: R is not close enough to A's inverse over the piece "
                       "(a smaller piece, or a better R)")
    Cm = [[_mag(c) for c in row] for row in C]
    return {"beta": beta, "C": C, "Cm": Cm, "rows": rows, "R": Rr, "AI": AI, "A0": A0, "par": par is not None}


def _core(Ai, bi, R, xt, iters, par=None, cc=None):
    """Steps 2-4 on the grid: {beta, C, rows, X} (integers, G), or LinError when beta >= 1. With `par` (_param) C and z
    are each the MEET of the interval form and the parametric form — both enclose, the meet is never wider. Sparse:
    a coefficient that is zero costs nothing (a ladder network's A has three entries a row). cc: step 2 already done
    by _contract for THIS Ai, R and par's matrix part (its right-hand side may differ) — reused, not recomputed."""
    n = len(Ai)
    if cc is None:
        cc = _contract(Ai, R, par)
    if cc["par"] != (par is not None):
        raise LinError("a reused contraction of another form")       # never mixed: the caller's bug, refused
    AI, Rr, A0 = cc["AI"], cc["R"], cc["A0"]
    BI = [_ivi(v) for v in bi]
    xr = [_rnd(v) for v in xt]
    # the interval form
    res = _residual(BI, _rows_nz(AI), xr)
    z2 = _Rtimes(Rr, {m: r for m, r in enumerate(res) if r[0] or r[1]}, n)
    if par is not None:
        B0 = [_ivi(v) for v in par["b0"]]
        res0 = _residual(B0, _rows_nz(A0), xr)
        zp = [list(c) for c in _Rtimes(Rr, {m: r for m, r in enumerate(res0) if r[0] or r[1]}, n)]
        # each quantity: w_j |R ([db_j] - [dA_j] x~)| into z (its w_j |R [dA_j]| is in C, _contract)
        for _nm, w, dA, db in par["terms"]:
            v = {}
            for i_, iv in db.items():
                d = _ivi(iv)
                v[i_] = [d[0] * G, d[1] * G]
            for (m, j), iv in dA.items():
                if xr[j]:
                    p_ = _smul(xr[j], _ivi(iv))
                    t = v.setdefault(m, [0, 0])
                    t[0] -= p_[1]
                    t[1] -= p_[0]
            vv = {m: (_dn(t[0]), _up(t[1])) for m, t in v.items()}
            for i, (lo2, hi2) in enumerate(_Rtimes(Rr, vv, n)):
                if lo2 or hi2:
                    rad = _up(max(abs(lo2), abs(hi2)) * w.numerator, w.denominator)
                    zp[i][0] -= rad
                    zp[i][1] += rad
        z = [_meet((_dn(a[0]), _up(a[1])), (_dn(c[0]), _up(c[1]))) for a, c in zip(z2, zp)]
    else:
        z = [(_dn(a[0]), _up(a[1])) for a in z2]
    C, Cm, rows, beta = cc["C"], cc["Cm"], cc["rows"], cc["beta"]
    E = _err_box(z, C, Cm, rows, beta, iters)
    X = [(xr[i] + E[i][0], xr[i] + E[i][1]) for i in range(n)]
    return {"beta": beta, "C": C, "Cm": Cm, "rows": rows, "X": X, "R": Rr}


# The error e = z + C e has |e| <= |z| + |C| |e|; as rho(|C|) <= beta < 1, (I - |C|)^-1 = sum |C|^m >= 0, so ANY u
# with u >= |z| + |C| u bounds |e| <= u componentwise (u - |e| = (I - |C|)^-1 (...) >= 0). A candidate u is computed
# in floating point (untrusted) and VERIFIED here exactly — one product with |C|; a failed candidate falls back to
# the norm bound (it replaces rounds of the refinement, which cost n^2 per round and per tolerance).

def _fsolve(M, rhs):
    """Gaussian elimination in floats (a candidate only — never trusted)."""
    n = len(M)
    a = [row[:] + [rhs[i]] for i, row in enumerate(M)]
    for c in range(n):
        p = max(range(c, n), key=lambda r: abs(a[r][c]))
        if a[p][c] == 0:
            return None
        a[c], a[p] = a[p], a[c]
        piv = a[c][c]
        for r in range(c + 1, n):
            f = a[r][c] / piv
            if f:
                ar, ac = a[r], a[c]
                for j in range(c, n + 1):
                    ar[j] -= f * ac[j]
    x = [0.0] * n
    for i in range(n - 1, -1, -1):
        s_ = a[i][n] - sum(a[i][j] * x[j] for j in range(i + 1, n))
        x[i] = s_ / a[i][i]
    return x


def _lu_float(Cm):
    """I - |C| in floats, for candidates (one per piece)."""
    n = len(Cm)
    return [[(1.0 if i == j else 0.0) - Cm[i][j] / G for j in range(n)] for i in range(n)]


def _verified_u(zm, Cm, M, transpose=False):
    """A u >= 0 with u >= zm + |C| u (or, transposed, u^T >= zm^T + u^T |C|), integers on the grid — or None."""
    n = len(zm)
    Mt = [list(col) for col in zip(*M)] if transpose else M
    cand = _fsolve(Mt, [v / G for v in zm])
    if cand is None or any(v != v or v < 0 for v in cand):
        return None
    for infl in (1e-9, 1e-6, 1e-3):
        # relative slack and one grid unit — never an absolute one: on a fine grid it swamped the tiny components
        # (a 100-node ladder's x_99 ~ 3e-37 would get 1e-21 of absolute slack)
        u = [int(v * (1 + infl) * G) + 1 for v in cand]
        ok = True
        for i in range(n):
            if transpose:
                acc = sum(u[m] * Cm[m][i] for m in range(n) if u[m] and Cm[m][i])
            else:
                acc = sum(Cm[i][j] * u[j] for j in range(n) if u[j] and Cm[i][j])
            if u[i] * G < zm[i] * G + acc:
                ok = False
                break
        if ok:
            return u
    return None


def _err_box(z, C, Cm, rows, beta, iters):
    """The error box E (integers, G): by a verified u when one is found (componentwise), else by the norm bound;
    then `iters` rounds of the refinement. Each is an enclosure of e."""
    n = len(z)
    zm = [_mag(zi) for zi in z]
    deltaG = _up(max(zm) * G, G - beta)                         # |e|_inf <= max|z| / (1 - beta), on the grid
    E = [(-_up(rows[i] * deltaG) - zm[i], _up(rows[i] * deltaG) + zm[i]) for i in range(n)]
    u = _verified_u(zm, Cm, _lu_float(Cm)) if n > 1 else None
    if u is not None:
        for i in range(n):
            cu = _up(sum(Cm[i][j] * u[j] for j in range(n) if u[j] and Cm[i][j]))
            E[i] = (max(E[i][0], z[i][0] - cu), min(E[i][1], z[i][1] + cu))   # e = z + C e, |C e| <= |C| u
    return _refine(z, C, E, iters) if iters else E


def _enclose(Ai, bi, R, xt, iters=0, par=None):
    """The kernel's steps 2-4: (beta, C, the enclosure of every x_i as Fractions). LinError when beta >= 1."""
    c = _core(Ai, bi, R, xt, iters, par)
    return F(c["beta"], G), c["C"], [_fiv(x) for x in c["X"]]


def _dread(A, b, names, k, qs, piece, R, xt, Ai, bi, iters=0, par=None):
    """Step 5 for many names at once: {name: the interval of d x_k / d name over the piece} (Fractions), a name with
    no derivative (min/max) -> its reason (a string). The derivatives come from `par` when given (built once)."""
    n = len(A)
    c = _core(Ai, bi, R, xt, iters, par)
    beta, C, Cm, rows, X, Rr = c["beta"], c["C"], c["Cm"], c["rows"], c["X"], c["R"]
    # step 5b: ONE y >= 0 with y^T (I - |C|) >= e_k^T |C|, verified; then for every tolerance
    #   |(C d)_k| <= (|C| |d|)_k <= e_k^T |C| (I - |C|)^-1 |zd| <= y^T |zd|
    y = _verified_u(Cm[k], Cm, _lu_float(Cm), transpose=True) if n > 1 else None
    by_name = {t[0]: (t[2], t[3]) for t in par["terms"]} if par is not None else None
    out = {}
    for name in names:
        try:
            if by_name is not None:
                dA, db = by_name.get(name, ({}, {}))
            else:
                dA, db = {}, {}
                for i in range(n):
                    if name in ZC._names(b[i]) if not isinstance(b[i], F) else False:
                        db[i] = _read(ZC.derivative(b[i], name), qs, piece)
                    for j in range(n):
                        if not isinstance(A[i][j], F) and name in ZC._names(A[i][j]):
                            dA[(i, j)] = _read(ZC.derivative(A[i][j], name), qs, piece)
        except ZC.NoDerivative as e:
            out[name] = f"{name}: {e}"
            continue
        r = {}                                                           # [dA x - db]_i, sparse
        for i, iv in db.items():
            d = _ivi(iv)
            r[i] = [-d[1] * G, -d[0] * G]
        for (i, j), iv in dA.items():
            p_ = _imul(_ivi(iv), X[j])
            t = r.setdefault(i, [0, 0])
            t[0] += p_[0]
            t[1] += p_[1]
        rr = {i: (_dn(t[0]), _up(t[1])) for i, t in r.items()}
        zd = [(_dn(a), _up(b_)) for a, b_ in _Rtimes(Rr, rr, n, -1)]    # d = -R r + C d  ->  z = -R r
        if y is not None and not iters:
            # d_k = zd_k + (C d)_k and |(C d)_k| <= y^T |zd| (step 5b): one product per tolerance
            cy = _up(sum(y[m] * _mag(zd[m]) for m in range(n) if y[m]))
            lo, hi = zd[k][0] - cy, zd[k][1] + cy
            dG = _up(max(_mag(zi) for zi in zd) * G, G - beta)
            nb = _up(rows[k] * dG) + _mag(zd[k])                          # the norm bound, met with it
            out[name] = _fiv((max(lo, -nb), min(hi, nb)))
            continue
        out[name] = _fiv(_err_box(zd, C, Cm, rows, beta, iters)[k])
    return out


# ── ELEMENTS THAT ENTER BY ONE LAYER (step 6, 2026-10-15) ─────────────────────────────────────────────────────────
# Wide tolerances on every part (all +-5 %, +-10 %) defeated the sign read of step 5: one enclosure of d x_k / d p over
# a wide piece. Most quantities of a linear circuit enter by ONE LAYER: dA/dp = g(p) u v^T and db/dp = g(p) kappa u
# with CONSTANT u, v, kappa (a resistor between two nodes: u = v = e_a - e_b, g = -1/R^2; a source in series: kappa =
# its voltage). Then, with A y = u and A^T mu = v,
#   d x_k / d p = -A^-1 (dA x - db) = -g (v^T x - kappa) y_k = -g * y_k * (mu^T b - kappa),
# a product of three scalars — each enclosed ON ITS OWN (two systems with a constant right-hand side), so a sign is
# proved where the product's single enclosure loses it. And integrating, A(p) = A(p0) + (phi(p) - phi(p0)) u v^T,
# b likewise (phi' = g): x_k is a LINEAR-FRACTIONAL function of phi(p), with no pole where A stays nonsingular — so
# x_k is MONOTONE in p along every line, whatever the other quantities are: its extremes over a piece sit on the two
# faces p = lo and p = hi (the "vertex" leaf).
# The structure is PROVED, not assumed: each identity  E == 0  (an entry of dA/dp against u_i v_j g, of db/dp against
# kappa u_i g) is checked by exact evaluation on a grid — E's numerator has degree at most d_x in each name x (bounded
# from E's tree), so if E vanishes on a grid of d_x + 1 values per name, the numerator is the zero polynomial
# (the combinatorial Nullstellensatz, Alon 1999) and E is identically zero. Candidates u, v, kappa are read at one
# point; only the exact check decides.

def _ev_exact(node, env):
    """A node's exact value at a point (rational operations only), or None (a function, a pole)."""
    if isinstance(node, F):
        return node
    if isinstance(node, int):
        return F(node)
    if isinstance(node, str):
        return env.get(node)
    if not isinstance(node, tuple):
        return None
    op, *args = node
    if op == "sum":
        vals = [_ev_exact(a, env) for a in args[0]]
        return None if any(v is None for v in vals) else sum(vals, ZERO)
    if op == "pow":
        base, ex = _ev_exact(args[0], env), args[1]
        if base is None or not isinstance(ex, (F, int)) or F(ex).denominator != 1:
            return None
        e = int(F(ex))
        return None if (base == 0 and e < 0) else base ** e
    if op not in ("add", "sub", "mul", "div"):
        return None
    x, y = _ev_exact(args[0], env), _ev_exact(args[1], env)
    if x is None or y is None:
        return None
    if op == "add":
        return x + y
    if op == "sub":
        return x - y
    if op == "mul":
        return x * y
    return None if y == 0 else x / y


def _deg(node, x):
    """(numerator degree, denominator degree) bounds in the name x of a rational node, or None."""
    if isinstance(node, (F, int)):
        return (0, 0)
    if isinstance(node, str):
        return (1, 0) if node == x else (0, 0)
    if not isinstance(node, tuple):
        return None
    op, *args = node
    if op == "sum":
        out = (0, 0)
        for a in args[0]:
            d = _deg(a, x)
            if d is None:
                return None
            out = (max(out[0] + d[1], d[0] + out[1]), out[1] + d[1])
        return out
    if op == "pow":
        d, ex = _deg(args[0], x), args[1]
        if d is None or not isinstance(ex, (F, int)) or F(ex).denominator != 1:
            return None
        e = int(F(ex))
        return (d[0] * e, d[1] * e) if e >= 0 else (d[1] * -e, d[0] * -e)
    if op not in ("add", "sub", "mul", "div"):
        return None
    a, c = _deg(args[0], x), _deg(args[1], x)
    if a is None or c is None:
        return None
    if op in ("add", "sub"):
        return (max(a[0] + c[1], c[0] + a[1]), a[1] + c[1])
    if op == "mul":
        return (a[0] + c[0], a[1] + c[1])
    return (a[0] + c[1], a[1] + c[0])


MAX_GRID = 4096


def _is_zero(node):
    """True only when the rational node is identically zero (an exact grid by the numerator's degrees); False when
    it is not, or when it cannot be decided here (a function, a grid too large, poles everywhere tried)."""
    names = sorted(ZC._names(node))
    degs = {}
    for x in names:
        d = _deg(node, x)
        if d is None:
            return False
        degs[x] = d[0]
    size = 1
    for x in names:
        size *= degs[x] + 1
    if size > MAX_GRID:
        return False
    # values 1, 2, 3, ... shifted past any pole met (a pole at a grid point is skipped by trying the next values)
    pts = {x: [F(3 + 7 * i, 5) for i in range(degs[x] + 1)] for x in names}
    for combo in itertools.product(*[pts[x] for x in names]):
        env = dict(zip(names, combo))
        v = _ev_exact(node, env)
        shift = 0
        while v is None and shift < 8:                  # a pole: move this point (each coordinate keeps distinct values)
            shift += 1
            env = {x: c + F(shift, 97) * (1 + names.index(x)) for x, c in zip(names, combo)}
            v = _ev_exact(node, env)
        if v is None or v != 0:
            return False
    return True


def _structure(A, b, name, qs, piece):
    """How `name` enters, every identity proved — or None.
    One layer in A:  {"g": node, "u": {i: c}, "v": {j: c}, "kappa": node}   dA = g u v^T, db = g kappa u, kappa free of
                     name (another quantity — a source in series — or a number);
    the right-hand side only: {"g": None, "h": node, "u": {i: c}}            dA = 0, db = h u."""
    n = len(A)
    dA, db = {}, {}
    try:
        for i in range(n):
            for j in range(n):
                if not isinstance(A[i][j], F) and name in ZC._names(A[i][j]):
                    d = ZC.derivative(A[i][j], name)
                    if not ZC._is0(d):
                        dA[(i, j)] = d
            if not isinstance(b[i], F) and name in ZC._names(b[i]):
                d = ZC.derivative(b[i], name)
                if not ZC._is0(d):
                    db[i] = d
    except ZC.NoDerivative:
        return None
    centre = {x: (F(lo) + F(hi)) / 2 for x, (lo, hi) in piece.items()}
    env = dict({x: qs[x]["lo"] for x in qs if isinstance(qs[x], dict) and "lo" in qs[x] and qs[x]["lo"] == qs[x].get("hi")},
               **centre)
    if not dA:
        # the right-hand side only: db = h u with a constant u
        if not db:
            return None
        i0 = min(db)
        h = db[i0]
        hv = _ev_exact(h, env)
        if not hv:
            return None
        u = {}
        for i, e in db.items():
            ev = _ev_exact(e, env)
            if ev is None:
                return None
            u[i] = ev / hv
            if not _is_zero(("sub", e, ("mul", u[i], h))):
                return None
        return {"g": None, "h": h, "u": {i: c for i, c in u.items() if c}}
    ref = min(dA)
    a0, c0 = ref
    g = dA[ref]
    gv = _ev_exact(g, env)
    if not gv:
        return None
    rows = sorted({i for i, _ in dA} | set(db))
    cols = sorted({j for _, j in dA})
    u, v = {}, {}
    for i in rows:
        e = dA.get((i, c0))
        ev = _ev_exact(e, env) if e is not None else ZERO
        if ev is None:
            return None
        u[i] = ev / gv
    for j in cols:
        e = dA.get((a0, j))
        ev = _ev_exact(e, env) if e is not None else ZERO
        if ev is None:
            return None
        v[j] = ev / gv
    for i in rows:
        for j in cols:
            c = u[i] * v[j]
            e = dA.get((i, j))
            if e is None:
                if c != 0:
                    return None
                continue
            if not _is_zero(("sub", e, ("mul", c, g))):
                return None
    # db = g kappa u: kappa from one row, free of name; every other row in proportion
    kappa = ZERO
    if db:
        i0 = next((i for i in rows if u[i] and i in db), None)
        if i0 is None:
            return None
        kappa = ("div", db[i0], ("mul", u[i0], g))
        try:
            if not _is_zero(ZC.derivative(kappa, name)):
                return None
        except ZC.NoDerivative:
            return None
        for i in rows:
            e = db.get(i)
            if e is None:
                if u[i] != 0:
                    return None
                continue
            if not _is_zero(("sub", ("mul", u[i0], e), ("mul", u[i], db[i0]))):
                return None
    return {"g": g, "u": {i: c for i, c in u.items() if c}, "v": {j: c for j, c in v.items() if c}, "kappa": kappa}


def _transpose_par(par, rhs):
    return {"A0": [list(col) for col in zip(*par["A0"])], "b0": rhs,
            "terms": [(t[0], t[1], {(j, i): iv for (i, j), iv in t[2].items()}, {}) for t in par["terms"]]}


def _cached(cache, key, make):
    """cache[key] = make() once — a LinError too (raised again on every later call, never retried)."""
    if cache is None:
        return make()
    if key not in cache:
        try:
            cache[key] = make()
        except LinError as e:
            cache[key] = e
    got = cache[key]
    if isinstance(got, LinError):
        raise got
    return got


def _factor_sign(A, b, k, qs, piece, R, Ai, bi, par, st, cache=None):
    """'+' / '-' — the sign of d x_k / d name over the piece by its factors (step 6) — or None. cache: a dict kept for
    ONE piece (one Ai, R, par) across its quantities — the two contractions, A's and A^T's, computed once."""
    n = len(A)
    lead = st["g"] if st["g"] is not None else st["h"]
    gi = _read(lead, qs, piece)
    if not (gi[0] > 0 or gi[1] < 0):
        return None
    u = st["u"]
    ui = [(u.get(i, ZERO), u.get(i, ZERO)) for i in range(n)]
    parU = {"A0": par["A0"], "b0": ui, "terms": [(t[0], t[1], t[2], {}) for t in par["terms"]]} if par else None
    yt = [sum((R[i][m] * c for m, c in u.items()), ZERO) for i in range(n)]
    cf = _cached(cache, "fwd", lambda: _contract(Ai, R, parU))
    Y = _fiv(_core(Ai, ui, R, yt, 0, parU, cf)["X"][k])
    if not (Y[0] > 0 or Y[1] < 0):
        return None
    sg = (1 if gi[0] > 0 else -1) * (1 if Y[0] > 0 else -1)
    if st["g"] is None:
        return "+" if sg > 0 else "-"              # d x_k / d name = h * (A^-1 u)_k
    v = st["v"]
    vi = [(v.get(i, ZERO), v.get(i, ZERO)) for i in range(n)]
    AiT, RT = _cached(cache, "T", lambda: ([list(col) for col in zip(*Ai)], [list(col) for col in zip(*R)]))
    mt = [sum((RT[i][m] * c for m, c in v.items()), ZERO) for i in range(n)]
    parT = _transpose_par(par, vi) if par else None
    cb = _cached(cache, "bwd", lambda: _contract(AiT, RT, parT))
    Mu = [_fiv(t) for t in _core(AiT, vi, RT, mt, 0, parT, cb)["X"]]
    ka = st["kappa"]
    kap = (ka, ka) if isinstance(ka, F) else _read(ka, qs, piece)
    s_lo, s_hi = -kap[1], -kap[0]
    for i in range(n):
        if bi[i] != (ZERO, ZERO):
            ps = (Mu[i][0] * bi[i][0], Mu[i][0] * bi[i][1], Mu[i][1] * bi[i][0], Mu[i][1] * bi[i][1])
            s_lo += min(ps)
            s_hi += max(ps)
    if not (s_lo > 0 or s_hi < 0):
        return None
    sg = -sg * (1 if s_lo > 0 else -1)              # d x_k / d name = -g * y_k * (mu^T b - kappa)
    return "+" if sg > 0 else "-"


def _signs(A, b, names_signs, k, qs, piece, R, xt, Ai, bi, iters=0, par=None, structs=None):
    """Step 5: for each (name, sign), does d x_k / d name keep that sign over the piece? -> the first failure or None."""
    got = _dread(A, b, list(names_signs), k, qs, piece, R, xt, Ai, bi, iters, par)
    cache = {}                                            # one piece: its contractions computed once
    for name, sg in names_signs.items():
        d = got[name]
        if not isinstance(d, str) and (d[0] >= 0 if sg == "+" else d[1] <= 0):
            continue
        st = (structs or {}).get(name)
        if st is not None and _factor_sign(A, b, k, qs, piece, R, Ai, bi, par, st, cache) == sg:
            continue                                      # step 6: three factors, each enclosed on its own
        if isinstance(d, str):
            return d
        lo, hi = d
        return f"{name}: d/d{name} of the target reads [{float(lo):.4g}, {float(hi):.4g}] on the piece, not {sg}"
    return None


def _solve_point(A, b, qs, piece, k):
    """x_k at a point, exactly: Gaussian elimination in fractions (partial pivoting by a non-zero pivot)."""
    n = len(A)
    M = []
    for i in range(n):
        row = []
        for e in A[i] + [b[i]]:
            lo, hi = _read(e, qs, piece)
            if lo != hi:
                raise LinError("a coefficient is not a single number at the point")
            row.append(lo)
        M.append(row)
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None:
            raise LinError("the system is singular at the point")
        M[c], M[p] = M[p], M[c]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c] / M[c][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return M[k][n] / M[k][k]


def _fr(s):
    return s if isinstance(s, F) else F(s)


def check(laws, unknowns, qs, target, op, bound, cert):
    """Is `target op bound` over the quantities' whole box, target an unknown of the linear `laws`? -> (True, pieces)
    or (False, reason). qs: ZTL's quantities (parse_quantities); the box is every name's [lo, hi] there."""
    if op not in ("<=", ">="):
        return False, f"op {op!r}: only <= and >= are certified"
    unknowns = list(unknowns)
    if target not in unknowns:
        return False, f"{target!r} is not an unknown of the system"
    try:
        A, b = system(laws, unknowns, qs)
    except LinError as e:
        return False, f"system: {e}"
    k = unknowns.index(target)
    names = sorted({n for row in A for e in row for n in ZC._names(e)} | {n for e in b for n in ZC._names(e)})
    for n in names:
        if n not in qs:
            return False, f"{n}: a coefficient reads a name with no box"
    piece0 = {n: (qs[n]["lo"], qs[n]["hi"]) for n in names}
    bound = _fr(bound)
    pieces = [0]
    bits = 64
    if isinstance(cert, dict) and "tree" in cert:          # the root may name the grid: {"grid": bits, "tree": tree}
        bits, cert = cert.get("grid", 64), cert["tree"]
    structs = {}                                           # step 6: proved once per check (identities over all values)

    def struct(nm):
        if nm not in structs:
            structs[nm] = _structure(A, b, nm, qs, piece0)
        return structs[nm]

    def walk(node, piece, depth):
        if depth > 400:
            return "the tree is deeper than 400"
        if not isinstance(node, dict):
            return "a node is not an object"
        if "vertex" in node:
            # step 6: nm enters by one layer (proved) and A is nonsingular over the piece (beta < 1 with this R) —
            # x_k is linear-fractional in phi(nm), monotone along every line in nm: its extremes over the piece lie
            # on the faces nm = lo and nm = hi; each face is checked by its own subtree
            nm = node["vertex"]
            if nm not in piece or piece[nm][0] == piece[nm][1]:
                return f"vertex on {nm!r}, not a wide quantity of the piece"
            st = struct(nm)
            if st is None:
                return f"vertex on {nm!r}: it does not enter by one layer (or that could not be proved)"
            gi = _read(st["g"] if st["g"] is not None else st["h"], qs, piece)
            if not (gi[0] > 0 or gi[1] < 0):
                return f"vertex on {nm!r}: d phi / d {nm} is not of one sign over the piece"
            try:
                R = [[_fr(v) for v in row] for row in node["R"]]
                xt = [_fr(v) for v in node["x"]]
                Ai, bi = _imatrix(A, qs, piece), [_read(e, qs, piece) for e in b]
                _core(Ai, bi, R, xt, 0, _param(A, b, qs, piece))      # beta < 1: nonsingular on the whole piece
            except (KeyError, TypeError, ValueError, ZeroDivisionError):
                return "a vertex node without a readable R and x"
            except LinError as e:
                return f"vertex on {nm!r}: {e}"
            lo, hi = piece[nm]
            return walk(node["lo"], dict(piece, **{nm: (lo, lo)}), depth + 1) or \
                walk(node["hi"], dict(piece, **{nm: (hi, hi)}), depth + 1)
        if "split" in node:
            nm, at = node["split"], _fr(node["at"])
            if nm not in piece:
                return f"split on {nm!r}, not a quantity of the system"
            lo, hi = piece[nm]
            if not lo < at < hi:
                return f"split {nm} at {at} is not inside [{lo}, {hi}]"
            return walk(node["lo"], dict(piece, **{nm: (lo, at)}), depth + 1) or \
                walk(node["hi"], dict(piece, **{nm: (at, hi)}), depth + 1)
        kind = node.get("leaf")
        if kind == "exact":
            # every name of the system is a point here: the solution, exactly (Gaussian elimination in fractions)
            if any(lo != hi for lo, hi in piece.values()):
                return "an exact leaf on a piece that is not a point"
            try:
                xk = _solve_point(A, b, qs, piece, k)
            except LinError as e:
                return str(e)
            if op == "<=" and xk > bound or op == ">=" and xk < bound:
                return f"{target} = {xk} exactly at the point, not {op} {bound}"
            pieces[0] += 1
            return None
        iters = node.get("iter", 0)
        if not isinstance(iters, int) or not 0 <= iters <= 200:
            return "iter must be an integer in 0..200"
        try:
            R = [[_fr(v) for v in row] for row in node["R"]]
            xt = [_fr(v) for v in node["x"]]
        except (KeyError, TypeError, ValueError, ZeroDivisionError):
            return "a leaf without a readable R and x"
        if len(R) != len(unknowns) or any(len(r) != len(unknowns) for r in R) or len(xt) != len(unknowns):
            return "R or x has the wrong size"
        try:
            Ai, bi = _imatrix(A, qs, piece), [_read(e, qs, piece) for e in b]
            if kind == "enclose":
                _beta, _C, X = _enclose(Ai, bi, R, xt, iters, _param(A, b, qs, piece))
                lo, hi = X[k]
                if op == "<=" and hi > bound or op == ">=" and lo < bound:
                    return (f"the enclosure of {target} on the piece is [{float(lo):.6g}, {float(hi):.6g}], "
                            f"not {op} {float(bound):.6g}")
                pieces[0] += 1
                return None
            if kind == "pin":
                sg = node.get("signs")
                if not isinstance(sg, dict) or not sg or any(s not in ("+", "-") for s in sg.values()):
                    return "a pin leaf needs signs {name: '+' | '-'}"
                if any(nm not in piece for nm in sg):
                    return "a pin on a name that is not a quantity of the system"
                bad = _signs(A, b, sg, k, qs, piece, R, xt, Ai, bi, iters, _param(A, b, qs, piece),
                             {nm: struct(nm) for nm in sg})
                if bad:
                    return bad
                # the max (<=) sits at the end a sign points up to, the min (>=) at the other
                to = {nm: (piece[nm][1] if (s == "+") == (op == "<=") else piece[nm][0]) for nm, s in sg.items()}
                return walk(node.get("then"), dict(piece, **{nm: (v, v) for nm, v in to.items()}), depth + 1)
            return f"unknown leaf {kind!r}"
        except LinError as e:
            return str(e)

    try:
        with grid(bits):
            why = walk(cert, piece0, 0)
    except LinError as e:
        why = str(e)
    return (False, why) if why else (True, pieces[0])
