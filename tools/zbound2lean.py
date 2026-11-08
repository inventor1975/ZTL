"""zbound2lean — a requirement over a box of tolerances as a Lean THEOREM on VR's continuum (lean/ZBound.lean).

The curator, 2026-11-08: "важно, если стенд будет давать не только сертификат, но и доказательства". A requirement
`q op c` on a derived quantity q of a LINEAR system of laws (the stand's divider, a network's currents), for every
parameter vector in the box:

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


def _box_lean(params, box):
    """`fun i => cond (Nat.beq i 0) (some (lo, hi)) (cond ... none)`."""
    body = "none"
    for i in reversed(range(len(params))):
        lo, hi = box[params[i]]
        body = f"(cond (Nat.beq i {i}) (some ({Z.dy(lo)}, {Z.dy(hi)})) {body})"
    return f"fun i => {body}"


def bound_to_lean(laws, unknowns, qtext, target, reqs, name, depth=14, trees=None):
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
    body += f"end {name}\n" + "".join(f"#print axioms {name}.cleared{k}\n#print axioms {name}.req{k}\n"
                                         for k in range(len(forms)))
    if quotient:
        body += f"#print axioms {name}.q_pos\n"
    path = os.path.join(gen, name + ".lean")
    out = _run(body, path)
    ok = "error" not in out and out.count("does not depend on any axioms") == 2 * len(forms) + (1 if quotient else 0)
    # "refused" only when the kernel's check said FALSE; a resource limit is not a verdict (2026-11-08: ztl-stand
    # tasks/t14, maxRecDepth inside `decide +kernel`, was first reported as "refused")
    limit = any(w in out for w in ("maximum recursion depth", "deterministic timeout", "heartbeats", "Stack overflow"))
    res = {"status": "theorem" if ok else ("kernel limit" if limit else "refused"), "file": path, "params": params, "box": box,
           "quotient": quotient, "trees": trees, "out": out[:600],
           # var i of the theorem is scale[p] · p (an integer box) when exact; else p itself over a dyadic box
           "scale": scale}
    return res


def main():
    # the stand's divider (examples/divider-1pct-req-1pct.json, the design R1 = R2 = 1 kΩ, ±1 %)
    laws = ["Vin - Vout == I*R1", "Vout == I*R2"]
    qt = "Vin=5 credit, R1=[990,1010] credit, R2=[990,1010] credit, I=? credit, Vout=? credit"
    st = bound_to_lean(laws, ["I", "Vout"], qt, "Vout", [(">=", "2.475"), ("<=", "2.525")], "ZGenDivider")
    print({k: v for k, v in st.items() if k != "out"})


if __name__ == "__main__":
    main()
