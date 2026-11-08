"""zbound2lean — a requirement over a box of tolerances as a Lean THEOREM on VR's continuum (lean/ZBound.lean).

The curator, 2026-11-08: "важно, если стенд будет давать не только сертификат, но и доказательства". A requirement
`q op c` on a derived quantity q of a LINEAR system of laws (the stand's divider, a network's currents), for every
parameter vector in the box:

  0. ON THE LAWS (2026-11-09, the curator's "B/C — делаем"), when q is an unknown — or a polynomial expression
     of unknowns, `_expr_on_laws` (a power I*I*R) — of a system with rational
     coefficients: the laws as polynomial ROWS and a cofactor certificate (`_law_cert`); the kernel checks
     `Σ cᵢ·Rᵢ ≡ D·q − N` (`ZBound.law_value`) and the file proves `lawreq{k}`: the requirement for EVERY value of the
     unknowns satisfying the laws — the elimination below is then only the search, not trusted;
  1. q's expression from the laws — ZTL's own Cramer solution (zcertify.solve_system): `q = det_q / det`; beyond
     ZC.MAX_SYSTEM unknowns the same determinants by Bareiss (`_solve_big`, exact polynomial division); no laws — q
     an expression of the data (said, not hidden: this elimination is Python's exact algebra, not proved in Lean;
     the theorem is about the expression);
  2. pinned quantities substituted; when q's numerator and denominator are POLYNOMIALS (a linear system's Cramer
     solution always is), EXACT: each parameter p in [lo, hi] read as x/s (s the common denominator of its ends, x in
     an INTEGER box) and N, D multiplied by one positive factor into integer polynomials in x (`_scaled`) — the
     quotient unchanged, every corner exact; otherwise the box rounded OUTWARD to dyadics (checked in fractions);
  3. a bound `N/D <= p/r` CLEARED to `p·D − r·N >= 0` (`D > 0` on the box, checked by the kernel through `posOK`):
     a tight requirement (met exactly at a corner) stays provable — the corners of a polynomial read exactly;
  3b. on the exact path the cleared form is ALSO written as ONE polynomial in Horner form (`G`): the tree is found and
     checked on G, and `ZBound.bound_identX` carries the bound to `r·N − p·D` through the kernel's identity test
     (`identX`: ZPoly's normal forms agree) — a datum shared by N and D keeps its factor (ztl-stand tasks/t5);
  4. ZBound.findV (Lean, compiled `#eval`) PROPOSES a cover tree — monotone leaves, interval leaves, cuts — printed
     and pasted as a literal; the kernel checks only `chkV` (`decide +kernel`) and `bound_vrM` gives the theorem;
  5. a NEGATIVE CONTROL: the same tree against a bound tightened past the attained value must be refused.

Status: "theorem" (the kernel accepted), "no tree" (the search found none within its depth), "refused" (the kernel
did not accept), "kernel limit" (recursion / time limit inside the check — not a verdict), "not translated" (not a linear system, or a function ZXE lacks).
"""
import math
import os
import re
import subprocess
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
LEAN = os.path.join(ROOT, "lean")
sys.path.insert(0, ROOT)
sys.path.insert(0, HERE)

import zlaw2lean as Z  # noqa: E402
import zkraw2lean as K  # noqa: E402


TSTACK_KB = 400000
_MUTANT = {}            # sabotage switches for the bridge's negative controls (never set on the real path)


def _subst(node, pinned):
    if isinstance(node, str):
        return pinned.get(node, node)
    if isinstance(node, (F, int)):
        return node
    op, *args = node
    if op == "sum":
        return ("sum", [_subst(a, pinned) for a in args[0]])
    return (op, *[_subst(a, pinned) for a in args])


def _sqrt2exp(node):
    """√u as exp(½·ln u) — HERE only (the bound path): `posOK` makes the kernel check ln's argument ≥ δ > 0 on the
    whole box, so the two agree wherever the theorem speaks (ztl-stand real2/s02, the reduced stress). Not in the
    shared zlaw2lean.to_xe: the systems' path has no such check (its bridge keeps sqrt "not translated")."""
    if isinstance(node, tuple):
        if node[0] == "sqrt":
            return ("exp", ("mul", F(1, 2), ("ln", _sqrt2exp(node[1]))))
        if node[0] == "sum":
            return ("sum", [_sqrt2exp(a) for a in node[1]])
        return (node[0], *[_sqrt2exp(a) for a in node[1:]])
    return node


def _names(node, acc):
    if isinstance(node, str):
        acc.add(node)
    elif isinstance(node, tuple):
        for a in node[1:]:
            if isinstance(a, list):
                for b in a:
                    _names(b, acc)
            else:
                _names(a, acc)
    return acc


def _dy_out(x, up):
    x = F(x)
    if Z.is_dyadic(x):
        return x
    return Z.ceil_dy(x, 48) if up else Z.floor_dy(x, 48)


def _run(text, path):
    # atomic: two stands proving the same requirement at once (the same content hash, the same file) never read a
    # half-written file (ztl-stand --prove over many bricks in parallel, 2026-11-08)
    tmp = f"{path}.{os.getpid()}.tmp"
    with open(tmp, "w") as f:
        f.write(text)
    os.replace(tmp, path)
    # a thread stack of 400 MB (2026-11-08, ztl-stand tasks/t14: `1/((1 + r/12)^360 − 1)` — the kernel forcing 360
    # nested interval products overflowed the default stack from n ≈ 300 on; MEASURED: with --tstack it reads in 0.7 s).
    # The check is the same; only the stack the kernel runs on is larger.
    r = subprocess.run(["lake", "env", "lean", f"--tstack={TSTACK_KB}", path], cwd=LEAN, capture_output=True,
                       text=True, timeout=3000)
    return r.stdout + r.stderr


def _padd(a, b, sg=1):
    out = dict(a)
    for m, c in b.items():
        out[m] = out.get(m, F(0)) + sg * c
        if out[m] == 0:
            del out[m]
    return out


def _pmul(a, b):
    out = {}
    for m1, c1 in a.items():
        for m2, c2 in b.items():
            m = tuple(x + y for x, y in zip(m1, m2))
            out[m] = out.get(m, F(0)) + c1 * c2
            if out[m] == 0:
                del out[m]
    return out


def _rnorm(N, D, n):
    """A zero numerator drops its denominator; a constant denominator folds into the numerator. (2026-11-08, ztl-stand
    blind/b01: Cramer's zero cofactor terms `0 · (G·d⁴/(8·Dm³·n))` multiplied every term's denominator into D —
    gap = (Lins − lift) − (n + 2)·d became a quotient of degree-20 polynomials and no tree was found.)"""
    one = {(0,) * n: F(1)}
    if not N:
        return {}, one
    if len(D) == 1 and (0,) * n in D:
        c = D[(0,) * n]
        return {m: v / c for m, v in N.items()}, one
    return N, D


def _rat(node, idx):
    r = _rat0(node, idx)
    return None if r is None else _rnorm(r[0], r[1], len(idx))


def _rat0(node, idx):
    """A RATIONAL node -> (numerator, denominator) polynomials {exponent tuple: Fraction}, or None (a function:
    exp, ln, a fractional power — not a quotient of polynomials). A linear system's Cramer solution, and any
    rational expression of it (P = I*I*R), is one."""
    n = len(idx)
    one = {(0,) * n: F(1)}
    if isinstance(node, (F, int)):
        return ({(0,) * n: F(node)} if node else {}), one
    if isinstance(node, str):
        if node not in idx:
            return None
        e = [0] * n; e[idx[node]] = 1
        return {tuple(e): F(1)}, one
    op = node[0]
    if op == "sum":
        acc = ({}, one)
        for x in node[1]:
            r = _rat(x, idx)
            if r is None:
                return None
            acc = (_padd(_pmul(acc[0], r[1]), _pmul(r[0], acc[1])), _pmul(acc[1], r[1]))
        return acc
    if op in ("mul", "div"):    # 0 · u = 0 and 0 / u = 0 whatever u is (VR's total law: 0 · u⁻¹ = 0) — a pinned zero
        x = _rat(node[1], idx)  # before a table the reader lacks (ztl-stand real3/s07: P = 0 times an `ifpos` table)
        if x is not None and not x[0]:
            return {}, one
    if op == "mul":
        y = _rat(node[2], idx)
        if y is not None and not y[0]:
            return {}, one
    if op in ("add", "sub", "mul", "div"):
        x, y = _rat(node[1], idx), _rat(node[2], idx)
        if x is None or y is None:
            return None
        (a, b), (c, d) = x, y
        if op == "mul":
            return _pmul(a, c), _pmul(b, d)
        if op == "div":
            return (_pmul(a, d), _pmul(b, c)) if c else None
        return _padd(_pmul(a, d), _pmul(c, b), 1 if op == "add" else -1), _pmul(b, d)
    if op == "neg":
        x = _rat(node[1], idx)
        return None if x is None else ({m: -c for m, c in x[0].items()}, x[1])
    if op == "pow" and isinstance(node[2], (F, int)) and F(node[2]).denominator == 1 and node[2] >= 0:
        x = _rat(node[1], idx)
        if x is None:
            return None
        N, D = one, one
        for _ in range(int(node[2])):
            N, D = _pmul(N, x[0]), _pmul(D, x[1])
        return N, D
    return None


def _poly_xe(P, n):
    """An integer polynomial as XE text in a greedy multivariate HORNER form: the variable in the most monomials
    factored out first, recursively. (2026-11-08, ztl-stand tasks/t5-divider-tcr: the expanded monomials read
    R1·(40000·T − 10⁶)·a1 as two terms in R1, the slope in a1 straddled 0 on every box and no monotone leaf passed;
    factored, the slope reads R1·(40000·T − 10⁶) and has one sign on each side of T = 25.)"""
    for c in P.values():
        assert c.denominator == 1
    return _horner({m: c for m, c in P.items() if c}, n)


def _horner(P, n):
    if not P:
        return Z.cst(0)
    cnt = [sum(1 for m in P if m[i] > 0) for i in range(n)]
    i = max(range(n), key=lambda j: (cnt[j], -j)) if n else 0
    if not n or cnt[i] == 0:
        return Z.cst(P.get((0,) * n, F(0)))
    has = {tuple(e - (1 if j == i else 0) for j, e in enumerate(m)): c for m, c in P.items() if m[i] > 0}
    rest = {m: c for m, c in P.items() if m[i] == 0}
    t = f"(.mul (.var {i}) {_horner(has, n)})"
    return t if not rest else f"(.add {_horner(rest, n)} {t})"


def _peval(P, x):
    tot = F(0)
    for m, c in P.items():
        t = c
        for xi, e in zip(x, m):
            t *= F(xi) ** e
        tot += t
    return tot


def _scaled(node, params, qs):
    """EXACT, no rounding (2026-11-08: a 27 ohm ±1 % box [26.73, 27.27] rounded outward to dyadics broke a
    requirement met exactly at a corner — ztl-stand examples/power-16thW-or-quarterW.json, `no tree`). Each
    parameter p_i in [lo_i, hi_i] is read as x_i / s_i with s_i the common denominator of its ends, so x_i lies in
    an INTEGER box; N and D are multiplied by the same positive factor Π s_i^k_i · L, turning both into integer
    polynomials in x — the quotient is unchanged and every corner reads exactly. None: not polynomials."""
    idx = {p: i for i, p in enumerate(params)}
    r = _rat(node, idx)
    if r is None or not r[1]:
        return None
    PN, PD = r
    n = len(params)
    s = [math.lcm(F(qs[p]["lo"]).denominator, F(qs[p]["hi"]).denominator) for p in params]
    k = [max([m[i] for m in list(PN) + list(PD)] or [0]) for i in range(n)]

    def sub(P):
        out = {}
        for m, c in P.items():
            f = c
            for i in range(n):
                f *= F(s[i]) ** (k[i] - m[i])
            out[m] = f
        return out
    N2, D2 = sub(PN), sub(PD)
    L = 1
    for c in list(N2.values()) + list(D2.values()):
        L = math.lcm(L, c.denominator)
    N2 = {m: c * L for m, c in N2.items()}
    D2 = {m: c * L for m, c in D2.items()}
    box = {p: (F(qs[p]["lo"]) * s[i], F(qs[p]["hi"]) * s[i]) for i, p in enumerate(params)}
    assert all(a.denominator == 1 and b.denominator == 1 for a, b in box.values())
    # the identity N2(x)/D2(x) = N(p)/D(p), x_i = s_i p_i, at two points (exact algebra, said: Python, not Lean)
    for t in (F(1, 3), F(5, 7)):
        p = [F(qs[q]["lo"]) + t * (F(qs[q]["hi"]) - F(qs[q]["lo"])) for q in params]
        x = [p[i] * s[i] for i in range(n)]
        if _peval(PD, p) != 0:
            assert _peval(N2, x) * _peval(PD, p) == _peval(PN, p) * _peval(D2, x)
    return N2, D2, box, dict(zip(params, s))


def _pdivexact(a, b):
    """a / b for multivariate polynomials when b divides a (Bareiss guarantees it): lex-leading terms; a remainder
    is an error, never rounded away."""
    lb = max(b)
    cb = b[lb]
    q, r = {}, dict(a)
    while r:
        lr = max(r)
        if any(x < y for x, y in zip(lr, lb)):
            raise ValueError("Bareiss: a division that is not exact")
        m = tuple(x - y for x, y in zip(lr, lb))
        c = r[lr] / cb
        q[m] = q.get(m, F(0)) + c
        r = _padd(r, _pmul({m: c}, b), -1)
    return q


def _bareiss(M, n_vars):
    """The determinant of a square matrix of polynomials, fraction-free (Bareiss), exact."""
    n = len(M)
    if n == 0:
        return {(0,) * n_vars: F(1)}
    M = [row[:] for row in M]
    prev, sign = {(0,) * n_vars: F(1)}, 1
    for k in range(n - 1):
        if not M[k][k]:
            for i in range(k + 1, n):
                if M[i][k]:
                    M[k], M[i] = M[i], M[k]
                    sign = -sign
                    break
            else:
                return {}
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                M[i][j] = _pdivexact(_padd(_pmul(M[i][j], M[k][k]), _pmul(M[i][k], M[k][j]), -1), prev)
        prev = M[k][k]
    d = M[n - 1][n - 1]
    return d if sign > 0 else {m: -c for m, c in d.items()}


def _pnode(P, names):
    """A polynomial back as a node over the parameters' names."""
    terms = []
    for m, c in sorted(P.items()):
        t = c
        for i, e in enumerate(m):
            if e:
                v = names[i] if e == 1 else ("pow", names[i], F(e))
                t = ("mul", t, v)
        terms.append(t)
    return ("sum", terms) if terms else F(0)


def _solve_big(laws, unknowns, qs, pinned):
    """A linear system of MORE than ZC.MAX_SYSTEM unknowns (2026-11-08: ztl-stand had 20 requirements on systems
    of 7–10 unknowns, refused by Cramer's n! terms): the coefficients read as rational functions of the box's
    parameters (`_rat`), each row cleared of its denominators, and u_j = det_j / det by BAREISS — exact polynomial
    arithmetic, the divisions checked exact. Python's algebra, like Cramer's: said, not proved in Lean."""
    import znumjudge as ZJ
    import zcertify as ZC
    us = sorted(set(unknowns))
    rows = []
    for law in laws:
        if law.count("==") != 1:
            raise ValueError(f"not one equality: {law!r}")
        l, r = law.split("==")
        a = ZC._lin(ZJ._parse_arith(l, qs), set(us))
        b = ZC._lin(ZJ._parse_arith(r, qs), set(us))
        row = dict(a)
        for k, v in b.items():
            row[k] = ("sub", row[k], v) if k in row else ("sub", F(0), v)
        rows.append({k: _subst(v, pinned) for k, v in row.items()})
    if len(rows) != len(us):
        raise ValueError(f"{len(rows)} equalities for {len(us)} unknowns: not a square system")
    names = sorted({n for row in rows for v in row.values() for n in _names(v, set())
                    if n in qs and n not in pinned and n not in us})
    idx = {n: i for i, n in enumerate(names)}
    nv = len(names)
    A, rhs = [], []
    for row in rows:
        ents = {}
        for k, v in row.items():
            rv = _rat(v, idx)
            if rv is None:
                raise ValueError("a coefficient is not a rational function of the data")
            ents[k] = rv
        Dprod = {(0,) * nv: F(1)}
        for (_, Dk) in ents.values():
            Dprod = _pmul(Dprod, Dk)
        cleared = {k: _pdivexact(_pmul(Nk, Dprod), Dk) for k, (Nk, Dk) in ents.items()}
        A.append([cleared.get(u, {}) for u in us])
        rhs.append({m: -c for m, c in cleared.get(1, {}).items()})
    det = _bareiss(A, nv)
    if not det:
        raise ValueError("the determinant is identically zero")
    sol = {}
    for j, u in enumerate(us):
        Aj = [r[:j] + [rhs[i]] + r[j + 1:] for i, r in enumerate(A)]
        sol[u] = ("div", _pnode(_bareiss(Aj, nv), names), _pnode(det, names))
    return sol


def _law_cert(laws, unknowns, qs, pinned, target):
    """THE LAWS AS ROWS, AND A COFACTOR CERTIFICATE (2026-11-09, the curator's "B/C — делаем").

    Each law read as a polynomial row `R_i = Σ_k A_ik(x)·u_k − b_i(x)` over the box's parameters x (each scaled to
    an integer box, x = s·p) and the unknowns u (variables past the parameters): the law's sides by ZC._lin, every
    coefficient a rational function (`_rat`), the row multiplied by its denominators and one positive constant —
    a LOCAL reading of each law (Python, said). The certificate c is the adjugate's row j: c_i = det(A with row i
    replaced by e_j) — so that Σ_i c_i·R_i ≡ D·u_j − N_j, D = det A, as polynomials: the kernel checks THIS
    (`ZBound.identX`), and no elimination is trusted. None: a coefficient not rational, or not a square system."""
    import znumjudge as ZJ
    import zcertify as ZC
    us = sorted(set(unknowns))
    if target not in us or len(laws) != len(us) or not us:
        return None
    raw = []
    for law in laws:
        if law.count("==") != 1:
            return None
        l, r = law.split("==")
        a = ZC._lin(ZJ._parse_arith(l, qs), set(us))
        b = ZC._lin(ZJ._parse_arith(r, qs), set(us))
        row = dict(a)
        for k, v in b.items():
            row[k] = ("sub", row[k], v) if k in row else ("sub", F(0), v)
        raw.append({k: _sqrt2exp(_subst(v, pinned)) for k, v in row.items()})
    params = sorted({n for row in raw for v in row.values() for n in _names(v, set())
                     if n in qs and n not in pinned and n not in us})
    for n in params:
        if isinstance(qs[n]["lo"], float) or isinstance(qs[n]["hi"], float):
            return None
    m, n = len(params), len(us)
    idx = {p: i for i, p in enumerate(params)}
    sc = [math.lcm(F(qs[p]["lo"]).denominator, F(qs[p]["hi"]).denominator) for p in params]

    def scale(P):                       # p_i = x_i / s_i
        out = {}
        for mo, c in P.items():
            f = c
            for i, e in enumerate(mo):
                f /= F(sc[i]) ** e
            out[mo] = f
        return out
    A, bvec = [], []
    for row in raw:
        ents = {}
        for k, v in row.items():
            rv = _rat(v, idx)
            if rv is None or not rv[1]:
                return None
            ents[k] = (scale(rv[0]), scale(rv[1]))
        Dp = {(0,) * m: F(1)}
        for (_, Dk) in ents.values():
            Dp = _pmul(Dp, Dk)
        cl = {k: _pdivexact(_pmul(Nk, Dp), Dk) for k, (Nk, Dk) in ents.items()}
        L = 1
        for P in cl.values():
            for c in P.values():
                L = math.lcm(L, c.denominator)
        cl = {k: {mo: c * L for mo, c in P.items()} for k, P in cl.items()}
        A.append([cl.get(u, {}) for u in us])
        bvec.append({mo: -c for mo, c in cl.get(1, {}).items()})
    j = us.index(target)
    D = _bareiss(A, m)
    if not D:
        return None
    unit = [({(0,) * m: F(1)} if k == j else {}) for k in range(n)]
    cert = [_bareiss(A[:i] + [unit] + A[i + 1:], m) for i in range(n)]
    N = {}
    for i in range(n):
        N = _padd(N, _pmul(cert[i], bvec[i]))
    box = {p: (F(qs[p]["lo"]) * sc[i], F(qs[p]["hi"]) * sc[i]) for i, p in enumerate(params)}
    x0 = [(box[p][0] + box[p][1]) / 2 for p in params]
    if _peval(D, x0) < 0:
        cert = [{mo: -c for mo, c in P.items()} for P in cert]
        D, N = {mo: -c for mo, c in D.items()}, {mo: -c for mo, c in N.items()}
    # rows over m + n variables; the identity checked here too (the kernel checks it again)
    ext = lambda P: {mo + (0,) * n: c for mo, c in P.items()}
    rows = []
    for i in range(n):
        R = {}
        for k in range(n):
            R = _padd(R, {mo + tuple(1 if t == k else 0 for t in range(n)): c for mo, c in A[i][k].items()})
        rows.append(_padd(R, ext(bvec[i]), -1))
    lhs = {}
    for i in range(n):
        lhs = _padd(lhs, _pmul(ext(cert[i]), rows[i]))
    rhs = _padd(_pmul(ext(D), {(0,) * m + tuple(1 if t == j else 0 for t in range(n)): F(1)}), ext(N), -1)
    assert _padd(lhs, rhs, -1) == {}, "the cofactor identity fails"
    for P in [D, N] + cert + rows:
        assert all(c.denominator == 1 for c in P.values())
    if _MUTANT.get("cert"):             # SABOTAGE (the bridge's other side): a certificate the kernel must refuse
        cert = [_padd(cert[0], {(0,) * m: F(1)})] + cert[1:]
    return {"params": params, "box": box, "scale": dict(zip(params, sc)), "D": D, "N": N, "cert": cert,
            "rows": rows, "m": m, "n": n, "j": j, "unknowns": us}


def _expr_on_laws(laws, unknowns, qs, pinned, target, reqs, name, depth):
    """An EXPRESSION of the unknowns (a power P = I*I*R) on the LAWS (2026-11-09, B/C, second step).

    For every unknown u_k the expression uses: its cofactor certificate (`_law_cert`) — the kernel proves
    D·u_k = N_k for every solution. E is read as a polynomial E'(x, u) = L·E (parameters scaled, L > 0 clearing the
    constants: said). With d its degree in u, Ê(x) = Σ_α e_α(x)·D^(d−|α|)·N^α, and for `r·E ≤ p`:
    Cl(x) = L·p·D^d − r·Ê(x) ≥ 0 on the box (a cover tree, the kernel), and the identity
    D^d·(L·p − r·E') − Cl ≡ Σ_k M_k·(D·u_k − N_k)   (M_k by telescoping D^a·u^α − N^α — no division)
    checked by `identX`; with D^d > 0, `r·E' ≤ L·p` for every point and EVERY solution of the laws.
    None: not this case (a division or a function in E, a coefficient not rational)."""
    import znumjudge as ZJ
    us = sorted(set(unknowns))
    try:
        enode = _sqrt2exp(_subst(ZJ._parse_arith(target, qs), pinned))
    except Exception:
        return None
    used = sorted(n for n in _names(enode, set()) if n in us)
    if not used:
        return None
    certs = {}
    for k in used:
        lc = _law_cert(laws, us, qs, pinned, k)
        if lc is None:
            return None
        certs[k] = lc
    base = certs[used[0]]
    params, m, n = base["params"], base["m"], base["n"]
    sc = [base["scale"][p] for p in params]
    if any(nm in qs and nm not in pinned and nm not in us and nm not in params for nm in _names(enode, set())):
        return None                     # E names a datum the laws do not: not handled here
    idx = {p_: i for i, p_ in enumerate(params)}
    idx.update({u: m + i for i, u in enumerate(us)})
    r_ = _rat(enode, idx)
    if r_ is None or not r_[1] or any(any(mo) for mo in r_[1]):
        return None                     # E must be a polynomial (a constant denominator)
    c0 = r_[1][(0,) * (m + n)]
    E = {}
    for mo, c in r_[0].items():         # p_i = x_i / s_i in E
        f = c / c0
        for i in range(m):
            f /= F(sc[i]) ** mo[i]
        E[mo] = f
    L = 1
    for c in E.values():
        L = math.lcm(L, c.denominator)
    E = {mo: c * L for mo, c in E.items()}
    d = max(sum(mo[m:]) for mo in E)
    D = base["D"]
    one_x = {(0,) * m: F(1)}

    def ppow(P, k):
        out = one_x
        for _ in range(k):
            out = _pmul(out, P)
        return out
    Nk = {us.index(k): certs[k]["N"] for k in used}
    ext = lambda P: {mo + (0,) * n: c for mo, c in P.items()}
    Ehat = {}
    terms = []                          # (e_alpha(x), alpha) per monomial of E
    for mo, c in E.items():
        ex = {mo[:m]: c}
        al = mo[m:]
        terms.append((ex, al))
        t = _pmul(ex, ppow(D, d - sum(al)))
        for k, a in enumerate(al):
            if a:
                t = _pmul(t, ppow(Nk[k], a))
        Ehat = _padd(Ehat, t)
    Dd = ppow(D, d)
    forms = []
    for op, cval in reqs:
        cval = F(cval)
        p_, rr = cval.numerator, cval.denominator
        P = p_ * L
        if op == "<=":
            Cl = _padd({mo: c * P for mo, c in Dd.items()}, {mo: c * rr for mo, c in Ehat.items()}, -1)
            sign = -1
        else:
            Cl = _padd({mo: c * rr for mo, c in Ehat.items()}, {mo: c * P for mo, c in Dd.items()}, -1)
            sign = 1
        # M_k by telescoping: D^a u^α − N^α = Σ_t [Π_{s<t} N_{k_s}]·(D u_{k_t} − N_{k_t})·[Π_{s>t} D u_{k_s}]
        M = {k: {} for k in range(n)}
        for ex, al in terms:
            seq = [k for k, a in enumerate(al) for _ in range(a)]
            pre = _pmul(ext(ex), ext(ppow(D, d - len(seq))))
            pre = {mo: c * sign * rr for mo, c in pre.items()}
            for t, k in enumerate(seq):
                f = pre
                for s_ in seq[:t]:
                    f = _pmul(f, ext(Nk[s_]))
                for s_ in seq[t + 1:]:
                    f = _pmul(f, _pmul(ext(D), {(0,) * m + tuple(1 if q == s_ else 0 for q in range(n)): F(1)}))
                M[k] = _padd(M[k], f)
        uvar = lambda k: {(0,) * m + tuple(1 if q == k else 0 for q in range(n)): F(1)}
        Z = {k: _padd(_pmul(ext(D), uvar(k)), ext(Nk[k]), -1) for k in Nk}
        W = (_padd({(0,) * (m + n): F(P)}, {mo: c * rr for mo, c in E.items()}, -1) if op == "<=" else
             _padd({mo: c * rr for mo, c in E.items()}, {(0,) * (m + n): F(P)}, -1))
        H = _padd(_pmul(ext(Dd), W), ext(Cl), -1)
        lhs = {}
        for k in Nk:
            lhs = _padd(lhs, _pmul(M[k], Z[k]))
        assert _padd(lhs, H, -1) == {}, "the telescoping identity fails"
        forms.append((op, P, rr, Cl, [M[k] for k in sorted(Nk)]))
    return {"params": params, "m": m, "n": n, "us": us, "box": base["box"], "scale": base["scale"], "D": D,
            "Nk": Nk, "certs": {us.index(k): certs[k]["cert"] for k in used}, "rows": base["rows"], "E": E, "d": d,
            "L": L, "forms": forms}


def _expr_lean(ex, target, name, depth):
    """The Lean file of `_expr_on_laws`; returns (status, file, out, trees)."""
    m, n, d = ex["m"], ex["n"], ex["d"]
    params = ex["params"]
    gen = os.path.join(LEAN, "gen"); os.makedirs(gen, exist_ok=True)
    ks = sorted(ex["Nk"])
    U = lambda k: f"(.var {m + k})"
    head = f"""import ZBound
open VR VR.Numbers ZNumBin ZField ZPoly ZIv ZXE ZRealCF ZRootDiv ZBound
set_option maxRecDepth 100000
namespace {name}
def B : Box := {_box_lean(params, ex["box"])}
def xD : XE := {_poly_xe(ex["D"], m)}
"""
    vs = "[" + ", ".join(str(i) for i in range(m)) + "]"
    probe = head + "".join(
        f'def Cl{i} : XE := {_poly_xe(f[3], m)}\n#eval IO.println (match findV true Cl{i} {Z.dy(0)} {vs} {depth} B with '
        f'| some t => "TREE" ++ toString {i} ++ " " ++ t.txt | none => "NOTREE" ++ toString {i})\n'
        for i, f in enumerate(ex["forms"])) + f"end {name}\n"
    out = _run(probe, os.path.join(gen, name + "_probe.lean"))
    trees = {}
    for i in range(len(ex["forms"])):
        mt = re.search(rf"^TREE{i} (.*)$", out, re.M)
        if not mt:
            return "no tree", None, out[:400], {}
        trees[i] = mt.group(1)
    body = head + f"""/-- The laws as rows (vars {m}..{m + n - 1}: {", ".join(ex["us"])}). -/
def rows : List XE := [{", ".join(_poly_xe(R, m + n) for R in ex["rows"])}]
/-- `{target}`, read as a polynomial times {ex["L"]} (parameters scaled). -/
def E : XE := {_poly_xe(ex["E"], m + n)}
"""
    for k in ks:
        body += f"""def xN{k} : XE := {_poly_xe(ex["Nk"][k], m)}
def cert{k} : List XE := [{", ".join(_poly_xe(C, m) for C in ex["certs"][k])}]
theorem law_val{k} (y : Nat → RExpr) (hy : InBox rCF B y) (hl : ∀ r, List.Mem r rows → rCF.r (evR y r) rCF.zero) :
    rCF.r (rCF.mul (evR y xD) (evR y {U(k)})) (evR y xN{k}) :=
  law_value hy (cs := cert{k}) hl (by decide +kernel) (by decide +kernel) (by decide +kernel)
"""
    zs = [f"(.sub (.mul xD {U(k)}) xN{k})" for k in ks]
    body += f"def Zs : List XE := [{', '.join(zs)}]\n"
    # the membership proof: one case per element
    mem = "intro z hz\n"
    ind = "    "
    for j, k in enumerate(ks):
        mem += f"{ind}cases hz with\n{ind}| head => exact sub_zero_of_eq (law_val{k} y hy hl)\n{ind}| tail _ hz =>\n"
        ind += "  "
    mem += f"{ind}cases hz\n"
    for i, (op, P, rr, Cl, Ms) in enumerate(ex["forms"]):
        R_, P_ = f"(XE.cst {Z.dy(rr)})", f"(XE.cst {Z.dy(P)})"
        W = f"(.sub {P_} (.mul {R_} E))" if op == "<=" else f"(.sub (.mul {R_} E) {P_})"
        stmt = (f"rCF.le (rCF.mul (evR y {R_}) (evR y E)) (evR y {P_})" if op == "<=" else
                f"rCF.le (evR y {P_}) (rCF.mul (evR y {R_}) (evR y E))")
        body += f"""def Cl{i} : XE := {_poly_xe(Cl, m)}
def T{i} : VT := {trees[i]}
theorem cl{i} : ∀ x : Nat → RExpr, InBox rCF B x → rCF.le (dv rOH {Z.dy(0)}) (evR x Cl{i}) :=
  bound_vrM (lo := true) (vs := {vs}) (T := T{i}) (by decide +kernel) (by decide +kernel)
def W{i} : XE := {W}
def H{i} : XE := .sub (.mul (.pow xD {d}) W{i}) Cl{i}
def Ms{i} : List XE := [{", ".join(_poly_xe(Mk, m + n) for Mk in Ms)}]
/-- **On the laws**: `{ex["L"]}·({target}) {op} {P}/{rr}` for EVERY point of the box and EVERY value of the unknowns
satisfying the laws. -/
theorem lawreq{i} (y : Nat → RExpr) (hy : InBox rCF B y) (hl : ∀ r, List.Mem r rows → rCF.r (evR y r) rCF.zero) :
    {stmt} := by
  have hz : ∀ z, List.Mem z Zs → rCF.r (evR y z) rCF.zero := by
    {mem}  have h0 : rCF.r (evR y H{i}) rCF.zero := combo_zero hy (cs := Ms{i}) hz (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have h1 : rCF.r (rCF.add (rCF.mul (evR y (.pow xD {d})) (evR y W{i})) (rCF.neg (evR y Cl{i}))) rCF.zero := h0
  have hpos : rCF.pos (evR y (.pow xD {d})) := (div_value hy (a := XE.cst (⟨⟨1, 0⟩, 0⟩ : D)) (b := .pow xD {d})
    (by decide +kernel)).1
  have hc : rCF.le rCF.zero (rCF.mul (evR y (.pow xD {d})) (evR y W{i})) :=
    rCF.le_respects (zv_isZ rOH (c := {Z.dy(0)}) rfl) (rCF.symm (eq_of_sub_zero h1)) (cl{i} y hy)
  exact le_of_sub_nonneg (nonneg_of_mul_pos hpos hc)
"""
    body += f"end {name}\n" + "".join(f"#print axioms {name}.law_val{k}\n" for k in ks) + "".join(
        f"#print axioms {name}.cl{i}\n#print axioms {name}.lawreq{i}\n" for i in range(len(ex["forms"])))
    path = os.path.join(gen, name + ".lean")
    out = _run(body, path)
    ok = "error" not in out and out.count("does not depend on any axioms") == len(ks) + 2 * len(ex["forms"])
    limit = any(w in out for w in ("maximum recursion depth", "deterministic timeout", "heartbeats", "Stack overflow"))
    return ("theorem" if ok else ("kernel limit" if limit else "refused")), path, out[:600], trees


def _box_lean(params, box):
    """`fun i => cond (Nat.beq i 0) (some (lo, hi)) (cond ... none)`."""
    body = "none"
    for i in reversed(range(len(params))):
        lo, hi = box[params[i]]
        body = f"(cond (Nat.beq i {i}) (some ({Z.dy(lo)}, {Z.dy(hi)})) {body})"
    return f"fun i => {body}"


def bound_to_lean(laws, unknowns, qtext, target, reqs, name, depth=14, trees=None, laws_mode=True):
    """laws: "lhs == rhs" strings; unknowns: the derived quantities; qtext: the sheet ("R1=[990,1010] credit, ...");
    target: the derived quantity, or an expression of the unknowns and the data ("I*I*R1"); reqs: [(">=", c) | ("<=", c)]; name: the Lean namespace. `trees`: given trees
    (the search skipped) — the negative control pastes an accepted tree under a false bound."""
    import znumjudge as ZJ
    import zcertify as ZC
    qs = ZJ.parse_quantities(qtext)[0]
    pinned = {n: F(q["lo"]) for n, q in qs.items() if n not in unknowns and q["lo"] == q["hi"]
              and not isinstance(q["lo"], float)}
    try:
        # no unknowns: the target is an expression of the data alone (ztl-stand real3/s07 — Cramer on an empty
        # system said "the determinant is identically zero"); more than ZC.MAX_SYSTEM unknowns: Bareiss (_solve_big)
        if not (unknowns or laws):
            sol = {}
        elif len(set(unknowns)) > ZC.MAX_SYSTEM:
            sol = _solve_big(laws, unknowns, qs, pinned)
        else:
            sol = ZC.solve_system(laws, unknowns, qs)
    except Exception as ex:
        return {"status": "not translated", "why": f"not a linear square system: {ex}"}
    if laws_mode and target not in sol and laws:
        ex = _expr_on_laws(laws, unknowns, qs, pinned, target, reqs, name, depth)
        if ex is not None:
            stt, path, out, trs = _expr_lean(ex, target, name, depth)
            if stt == "theorem" or stt == "refused":
                return {"status": stt, "file": path, "params": ex["params"], "box": ex["box"], "quotient": True,
                        "trees": trs, "out": out, "scale": ex["scale"], "about": "laws", "factor": ex["L"]}
            # no tree / a kernel limit on the laws: the expression path below is still tried
    if target in sol:
        node = sol[target]
    else:                   # an EXPRESSION of the unknowns and the data (P = I*I*R): the solutions substituted
        try:
            node = ZC._subst(ZJ._parse_arith(target, qs), sol)
        except Exception as ex:
            return {"status": "not translated", "why": f"the target {target!r}: {ex}"}
    node = _sqrt2exp(_subst(node, pinned))
    params = sorted(n for n in _names(node, set()) if n in qs and n not in pinned)
    for n in params:
        if isinstance(qs[n]["lo"], float) or isinstance(qs[n]["hi"], float):
            return {"status": "not translated", "why": f"{n} is unbounded"}
    idx = {n: i for i, n in enumerate(params)}
    quotient = isinstance(node, tuple) and node[0] == "div"
    Nn, Dn = (node[1], node[2]) if quotient else (node, F(1))
    law = _law_cert(laws, unknowns, qs, pinned, target) if laws_mode else None
    if law is not None:                              # the theorem on the LAWS: D, N from the rows, the box over all
        params, box, scale = law["params"], law["box"], law["scale"]     # the rows' parameters
        N2, D2 = law["N"], law["D"]
        sc = (N2, D2, box, scale)
    else:
        sc = _scaled(node, params, qs)
    scale = None
    if sc is not None:                               # exact: integer box, integer polynomials (see _scaled)
        N2, D2, box, scale = sc
        x0 = [(box[p][0] + box[p][1]) / 2 for p in params]
        if _peval(D2, x0) < 0:                       # a negative determinant: both signs turned
            N2, D2 = {m: -c for m, c in N2.items()}, {m: -c for m, c in D2.items()}
        quotient = True
        xe_N, xe_D = _poly_xe(N2, len(params)), _poly_xe(D2, len(params))
        xe_q = f"(.div {xe_N} {xe_D})"
    else:
        box = {n: (_dy_out(qs[n]["lo"], False), _dy_out(qs[n]["hi"], True)) for n in params}
        assert all(box[n][0] <= F(qs[n]["lo"]) and F(qs[n]["hi"]) <= box[n][1] for n in params)
        env = {n: float((box[n][0] + box[n][1]) / 2) for n in params}
        if quotient and K.fl(Dn, env) < 0:          # a negative determinant: both signs turned
            Nn, Dn = ("sub", F(0), Nn), ("sub", F(0), Dn)
        try:
            xe_q = Z.to_xe(("div", Nn, Dn) if quotient else node, idx)
            xe_N = Z.to_xe(Nn, idx) if quotient else None
            xe_D = Z.to_xe(Dn, idx) if quotient else None
        except ValueError as ex:
            return {"status": "not translated", "why": str(ex)}
    forms = []          # (label, XE text of the cleared form >= 0, c, side)
    for op, c in reqs:
        c = F(c)
        p, r = c.numerator, c.denominator
        if quotient:
            form = (f"(.sub (.mul {Z.cst(p)} xD) (.mul {Z.cst(r)} xN))" if op == "<=" else
                    f"(.sub (.mul {Z.cst(r)} xN) (.mul {Z.cst(p)} xD))")
        else:
            form = (f"(.sub {Z.cst(p)} (.mul {Z.cst(r)} xQ))" if op == "<=" else
                    f"(.sub (.mul {Z.cst(r)} xQ) {Z.cst(p)})")
        G = None
        if sc is not None:          # ONE polynomial, Horner (the factors N and D share kept); identX carries it to `form`
            Gp = (_padd({m: v * p for m, v in D2.items()}, {m: v * r for m, v in N2.items()}, -1) if op == "<=" else
                  _padd({m: v * r for m, v in N2.items()}, {m: v * p for m, v in D2.items()}, -1))
            G = _poly_xe(Gp, len(params))
        forms.append((op, c, form, G))
    gen = os.path.join(LEAN, "gen"); os.makedirs(gen, exist_ok=True)
    head = f"""import ZBound
open VR VR.Numbers ZNumBin ZField ZPoly ZIv ZXE ZRealCF ZRootDiv ZBound
set_option maxRecDepth 100000
namespace {name}
def B : Box := {_box_lean(params, box)}
def xQ : XE := {xe_q}
{"def xN : XE := " + xe_N if quotient else ""}
{"def xD : XE := " + xe_D if quotient else ""}
"""
    vs = "[" + ", ".join(str(i) for i in range(len(params))) + "]"
    probe = head + "".join(
        f'def F{k} : XE := {G or form}\n#eval IO.println (match findV true F{k} {Z.dy(0)} {vs} {depth} B with '
        f'| some t => "TREE" ++ toString {k} ++ " " ++ t.txt | none => "NOTREE" ++ toString {k})\n'
        for k, (_, _, form, G) in enumerate(forms)) + f"end {name}\n"
    given = trees
    out = _run(probe, os.path.join(gen, name + "_probe.lean")) if given is None else ""
    trees = dict(given) if given is not None else {}
    for k in range(len(forms) if given is None else 0):
        m = re.search(rf"^TREE{k} (.*)$", out, re.M)
        if not m:
            return {"status": "no tree", "why": f"requirement {forms[k][0]} {forms[k][1]}: no tree within depth {depth}",
                    "out": out[:400]}
        trees[k] = m.group(1)
    body = head
    if quotient:
        body += f"""theorem q_pos (x : Nat → RExpr) (hx : InBox rCF B x) :
    rCF.pos (evR x xD) ∧ rCF.r (rCF.mul (evR x xD) (evR x xQ)) (evR x xN) :=
  div_value hx (a := xN) (b := xD) (by decide +kernel)
"""
    for k, (op, c, form, G) in enumerate(forms):
        if G is None:
            body += f"""def F{k} : XE := {form}
def T{k} : VT := {trees[k]}
theorem cleared{k} : ∀ x : Nat → RExpr, InBox rCF B x → rCF.le (dv rOH {Z.dy(0)}) (evR x F{k}) :=
  bound_vrM (lo := true) (vs := {vs}) (T := T{k}) (by decide +kernel) (by decide +kernel)
"""
        else:
            body += f"""def F{k} : XE := {form}
/-- The same polynomial as `F{k}`, one Horner form (`identX`, checked by the kernel). -/
def G{k} : XE := {G}
def T{k} : VT := {trees[k]}
theorem cleared{k} : ∀ x : Nat → RExpr, InBox rCF B x → rCF.le (dv rOH {Z.dy(0)}) (evR x F{k}) :=
  bound_identX (lo := true) (G := G{k}) (vs := {vs}) (T := T{k}) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
"""
        # THE REQUIREMENT ITSELF, as `r·q ≤ p` / `p ≤ r·q` (q ≤ p/r without division): the cleared form, the
        # quotient's value and `ZBound.le_of_quotR` — the reading's glue is a theorem, not prose
        p, r = c.numerator, c.denominator
        R, P = f"(evR x (XE.cst {Z.dy(r)}))", f"(evR x (XE.cst {Z.dy(p)}))"
        stmt = (f"rCF.le (rCF.mul {R} (evR x xQ)) {P}" if op == "<=" else f"rCF.le {P} (rCF.mul {R} (evR x xQ))")
        if quotient:
            pf = (f"""  obtain ⟨hpos, hv⟩ := q_pos x hx
  exact {"le_of_quotR" if op == "<=" else "ge_of_quotR"} hpos hv (rCF.le_respects (zv_isZ rOH (c := {Z.dy(0)}) rfl) (rCF.refl _) (cleared{k} x hx))""")
        else:
            pf = (f"""  exact le_of_sub_nonneg (rCF.le_respects (zv_isZ rOH (c := {Z.dy(0)}) rfl) (rCF.refl _) (cleared{k} x hx))""")
        body += f"""/-- **The requirement** `q {op} {p}/{r}` for every point of the box. -/
theorem req{k} (x : Nat → RExpr) (hx : InBox rCF B x) : {stmt} := by
{pf}
"""
    nlaw = 0
    if law is not None:
        mm, nn = law["m"], law["n"]
        rows_xe = [_poly_xe(R, mm + nn) for R in law["rows"]]
        cert_xe = [_poly_xe(C, mm) for C in law["cert"]]
        U = f"(.var {mm + law['j']})"
        body += f"""/-! ## On the LAWS: every value of the unknowns satisfying them (vars {mm}..{mm + nn - 1}: {", ".join(law["unknowns"])}) -/
/-- The laws as rows `Σ A·u − b` (each law multiplied by its denominators, parameters scaled). -/
def rows : List XE := [{", ".join(rows_xe)}]
/-- The cofactor certificate: `Σ cᵢ·Rᵢ ≡ D·u − N`, checked by the kernel (`identX`). -/
def cert : List XE := [{", ".join(cert_xe)}]
theorem law_val (y : Nat → RExpr) (hy : InBox rCF B y) (hl : ∀ r, List.Mem r rows → rCF.r (evR y r) rCF.zero) :
    rCF.r (rCF.mul (evR y xD) (evR y {U})) (evR y xN) :=
  law_value hy (cs := cert) hl (by decide +kernel) (by decide +kernel) (by decide +kernel)
"""
        for k, (op, c, form, G) in enumerate(forms):
            p_, r_ = c.numerator, c.denominator
            R, P = f"(evR y (XE.cst {Z.dy(r_)}))", f"(evR y (XE.cst {Z.dy(p_)}))"
            stmt = (f"rCF.le (rCF.mul {R} (evR y {U})) {P}" if op == "<=" else
                    f"rCF.le {P} (rCF.mul {R} (evR y {U}))")
            body += f"""/-- **The requirement on the laws**: `{target} {op} {p_}/{r_}` for EVERY point of the box and EVERY value of
the unknowns satisfying the laws. -/
theorem lawreq{k} (y : Nat → RExpr) (hy : InBox rCF B y) (hl : ∀ r, List.Mem r rows → rCF.r (evR y r) rCF.zero) :
    {stmt} :=
  {"le_of_quotR" if op == "<=" else "ge_of_quotR"} (q_pos y hy).1 (law_val y hy hl)
    (rCF.le_respects (zv_isZ rOH (c := {Z.dy(0)}) rfl) (rCF.refl _) (cleared{k} y hy))
"""
        nlaw = 1 + len(forms)
    body += f"end {name}\n" + "".join(f"#print axioms {name}.cleared{k}\n#print axioms {name}.req{k}\n"
                                         for k in range(len(forms)))
    if quotient:
        body += f"#print axioms {name}.q_pos\n"
    if law is not None:
        body += f"#print axioms {name}.law_val\n" + "".join(f"#print axioms {name}.lawreq{k}\n"
                                                              for k in range(len(forms)))
    path = os.path.join(gen, name + ".lean")
    out = _run(body, path)
    ok = "error" not in out and out.count("does not depend on any axioms") == 2 * len(forms) + (1 if quotient else 0) + nlaw
    # "refused" only when the kernel's check said FALSE; a resource limit is not a verdict (2026-11-08: ztl-stand
    # tasks/t14, maxRecDepth inside `decide +kernel`, was first reported as "refused")
    limit = any(w in out for w in ("maximum recursion depth", "deterministic timeout", "heartbeats", "Stack overflow"))
    res = {"status": "theorem" if ok else ("kernel limit" if limit else "refused"), "file": path, "params": params, "box": box,
           "quotient": quotient, "trees": trees, "out": out[:600],
           # var i of the theorem is scale[p] · p (an integer box) when exact; else p itself over a dyadic box
           "scale": scale,
           # on the LAWS (the requirement for every value of the unknowns satisfying them), or on the expression
           "about": "laws" if law is not None else "expression"}
    return res


def main():
    # the stand's divider (examples/divider-1pct-req-1pct.json, the design R1 = R2 = 1 kΩ, ±1 %)
    laws = ["Vin - Vout == I*R1", "Vout == I*R2"]
    qt = "Vin=5 credit, R1=[990,1010] credit, R2=[990,1010] credit, I=? credit, Vout=? credit"
    st = bound_to_lean(laws, ["I", "Vout"], qt, "Vout", [(">=", "2.475"), ("<=", "2.525")], "ZGenDivider")
    print({k: v for k, v in st.items() if k != "out"})


if __name__ == "__main__":
    main()
