"""
zsystem — a SYSTEM of laws F(x, p) = 0: a solution in a cube, the only one there, for every parameter in its box.

The question `x = ?, y = ?` with a claim made of equations (`x*x + y*y = 1 & x = exp(y)`) is a system. Its answer
here is LOCAL and says so (curator's choice 2026-11-08, "first A, then B"): a cube C around a solution, the solution
exists in C and is unique there; solutions elsewhere are NOT excluded (that needs a search region and an exclusion of
the rest — the planned B).

THE CERTIFICATE (Krawczyk's test, the contraction form; the same three conditions the Lean kernel checks in
lean/ZKraw.lean and lean/ZKrawSys.lean): G(x) = x − Y·F(x) with a preconditioner Y,
  1. CONTRACTION: every row of I − Y·J(C × P) — J read entry by entry from the kernel's derivative
     (zcertify.derivative) over the cube and the parameter box — sums in absolute value to ≤ ½;
  2. INTO: G at the centre, read over the parameter box, widened by r/2, lies strictly inside C;
  3. Y INVERTIBLE: a second matrix Z with every row of |I − Z·Y| summing to ≤ ½ (exact rationals).
Then G maps C into itself and halves distances (a staircase of mean values, one coordinate at a time), so it has a
fixed point in C and only one (Banach); the fixed point is a zero of F (Y·F = 0 and Y invertible). All readings are
the kernel's (zcertify._reading), all arithmetic exact; the floats only PROPOSE (Newton, Y ≈ J⁻¹, Z ≈ J).
Lean: tools/zkraw2lean.py turns a system into a theorem of lean/ZKrawSys.lean (`sys_root`), checked by Lean's
kernel — a second, independent check (not run on the public server).
"""
import math
from fractions import Fraction as F

import zcertify as ZC


def _rd(e, qs, piece):
    """The kernel's reading, or None; ("never", None) when the law has NO value anywhere on the piece (an `ln` of a
    quantity never positive there, zfunc's NoReadings) — no solution can lie there."""
    try:
        return ZC._reading(e, qs, piece)
    except Exception as ex:                       # znum._NoReadings and its kin
        if "never" in str(ex):
            return "never"
        return None


def _mid(iv):
    return float((iv[0] + iv[1]) / 2)


def _point(qs, unknowns, x):
    return {n: (F(v), F(v)) for n, v in zip(unknowns, x)}


_FOPS1 = {"exp": math.exp, "ln": math.log, "log10": math.log10, "atan": math.atan, "tan": math.tan, "sin": math.sin,
          "cos": math.cos, "sqrt": math.sqrt}


def _ff(e, env):
    """The law in FLOATS — for the PROPOSAL only (Newton's steps). Nothing it says is trusted: every certificate is
    checked exactly by `check`. MEASURED 2026-11-08: the exact readings of sin/cos at points made the search of a
    2×2 system with sin take 37 s of 38 (zfunc's exact trigonometry); in floats it is microseconds. Any node it does
    not know, a domain error, an overflow — the caller falls back to the exact reading."""
    if isinstance(e, (int, F)):
        return float(e)
    if isinstance(e, str):
        return env[e]
    op, *args = e
    if op in _FOPS1:
        return _FOPS1[op](_ff(args[0], env))
    if op == "sum":
        return math.fsum(_ff(a, env) for a in args[0])
    if op in ("add", "sub", "mul", "div", "pow"):
        a, b = _ff(args[0], env), _ff(args[1], env)
        return {"add": a + b, "sub": a - b, "mul": a * b}[op] if op in ("add", "sub", "mul") else (
            a / b if op == "div" else a ** b)
    raise KeyError(op)


def _fenv(qs, unknowns, x, params_mid):
    env = {}
    for n, q in qs.items():
        try:
            env[n] = (float(q["lo"]) + float(q["hi"])) / 2
        except (KeyError, TypeError, ValueError):
            pass
    for n, (lo, hi) in params_mid.items():
        env[n] = float((lo + hi) / 2)
    env.update(zip(unknowns, (float(v) for v in x)))
    return env


def _fast(exprs, env):
    try:
        out = [_ff(g, env) for g in exprs]
    except (KeyError, ValueError, OverflowError, ZeroDivisionError, TypeError):
        return None
    return out if all(isinstance(v, float) and math.isfinite(v) for v in out) else None


def _fvals(laws, qs, unknowns, x, params_mid):
    fv = _fast(laws, _fenv(qs, unknowns, x, params_mid))
    if fv is not None:
        return fv
    piece = _point(qs, unknowns, x)
    piece.update(params_mid)
    out = []
    for g in laws:
        r = _rd(g, qs, piece)
        if r is None or r == "never":
            return None
        out.append(_mid(r))
    return out


def _jac(dlaws, qs, unknowns, x, params_mid):
    env = _fenv(qs, unknowns, x, params_mid)
    rows = [_fast(row, env) for row in dlaws]
    if all(r is not None for r in rows):
        return rows
    piece = _point(qs, unknowns, x)
    piece.update(params_mid)
    J = []
    for row in dlaws:
        rr = []
        for dg in row:
            r = _rd(dg, qs, piece)
            if r is None or r == "never":
                return None
            rr.append(_mid(r))
        J.append(rr)
    return J


def _solve(A, b):
    n = len(A)
    M = [list(map(float, row)) + [float(b[i])] for i, row in enumerate(A)]
    for c in range(n):
        p = max(range(c, n), key=lambda r: abs(M[r][c]))
        if abs(M[p][c]) < 1e-300:
            return None
        M[c], M[p] = M[p], M[c]
        for r in range(n):
            if r != c:
                f = M[r][c] / M[c][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [M[i][n] / M[i][i] for i in range(n)]


def _inv(A):
    n = len(A)
    cols = []
    for j in range(n):
        c = _solve(A, [1.0 if i == j else 0.0 for i in range(n)])
        if c is None:
            return None
        cols.append(c)
    return [[cols[j][i] for j in range(n)] for i in range(n)]


def _iv_scale(c, iv):
    a, b = c * iv[0], c * iv[1]
    return (min(a, b), max(a, b))


def _iv_add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def _amax(iv):
    return max(abs(iv[0]), abs(iv[1]))


def check(laws, unknowns, qs, cert):
    """(True, how) when the certificate {"centre": [...], "radius": r, "Y": [[...]], "Z": [[...]]} proves a unique
    solution in the cube, for every parameter vector in the sheet's boxes; else (False, reason). Exact."""
    d = len(unknowns)
    try:
        y = [F(str(v)) for v in cert["centre"]]
        r = F(str(cert["radius"]))
        Y = [[F(str(v)) for v in row] for row in cert["Y"]]
        Zm = [[F(str(v)) for v in row] for row in cert["Z"]]
    except (KeyError, ValueError, TypeError, ZeroDivisionError):
        return False, "certificate unreadable"
    if len(y) != d or len(Y) != d or len(Zm) != d or any(len(row) != d for row in Y + Zm) or len(laws) != d:
        return False, "the certificate does not have the system's size"
    if r <= 0:
        return False, "the radius is not positive"
    cube = {n: (y[i] - r, y[i] + r) for i, n in enumerate(unknowns)}
    # 1. contraction: the rows of I − Y·J over the cube × the parameter box
    J = []
    for g in laws:
        row = []
        for n in unknowns:
            iv = _rd(ZC.derivative(g, n), qs, cube)
            if iv is None or iv == "never":
                return False, f"no reading of d/d{n} of a law over the cube"
            row.append(iv)
        J.append(row)
    rows = []
    for k in range(d):
        s = F(0)
        for j in range(d):
            m = (F(1 if k == j else 0), F(1 if k == j else 0))
            acc = (F(0), F(0))
            for i in range(d):
                acc = _iv_add(acc, _iv_scale(Y[k][i], J[i][j]))
            m = (m[0] - acc[1], m[1] - acc[0])
            s += _amax(m)
        rows.append(s)
        if s > F(1, 2):
            return False, f"row {k} of I − Y·J sums to {float(s):.3g} > 1/2: no contraction proved"
    # 2. into: G(centre) ± r/2 inside the cube
    centre = {n: (y[i], y[i]) for i, n in enumerate(unknowns)}
    Gc = []
    for g in laws:
        iv = _rd(g, qs, centre)
        if iv is None or iv == "never":
            return False, "no reading of a law at the centre"
        Gc.append(iv)
    for k in range(d):
        acc = (F(0), F(0))
        for i in range(d):
            acc = _iv_add(acc, _iv_scale(Y[k][i], Gc[i]))
        lo, hi = y[k] - acc[1], y[k] - acc[0]
        if not (y[k] - r < lo - r / 2 and hi + r / 2 < y[k] + r):
            return False, f"G maps the cube out of itself at coordinate {unknowns[k]}"
    # 3. Y invertible: the rows of |I − Z·Y|
    for k in range(d):
        s = F(0)
        for j in range(d):
            p = sum((Zm[k][i] * Y[i][j] for i in range(d)), F(0))
            s += abs(F(1 if k == j else 0) - p)
        if s > F(1, 2):
            return False, f"row {k} of I − Z·Y sums to {float(s):.3g} > 1/2: Y not shown invertible"
    return True, (f"a solution in the cube of radius {r} around the centre, the only one there "
                  f"(contraction rows ≤ {float(max(rows)):.3g}); solutions elsewhere are not excluded")


def search(laws, unknowns, qs, guesses=None, radii=None):
    """Propose a certificate (Newton from several starts, Y ≈ J⁻¹, Z ≈ J, radii 2⁻²⁰ .. 2⁻⁴) and return the first the
    exact check accepts, with its result; or None."""
    d = len(unknowns)
    params = sorted(n for n in set().union(*[ZC._names(g) for g in laws]) if n in qs and n not in unknowns)
    params_mid = {n: (F(qs[n]["lo"] + qs[n]["hi"]) / 2,) * 2 for n in params
                  if not isinstance(qs[n]["lo"], float) and not isinstance(qs[n]["hi"], float)}
    dlaws = [[ZC.derivative(g, n) for n in unknowns] for g in laws]
    starts = guesses or [[0.5] * d, [1.0] * d, [-0.5] * d, [0.1] * d, [2.0] * d, [-1.0] * d]
    for x0 in starts:
        x = list(x0)
        ok = False
        for _ in range(60):
            fv = _fvals(laws, qs, unknowns, x, params_mid)
            Jv = _jac(dlaws, qs, unknowns, x, params_mid)
            if fv is None or Jv is None:
                break
            dx = _solve(Jv, fv)
            if dx is None:
                break
            x = [a - b for a, b in zip(x, dx)]
            if not all(math.isfinite(v) for v in x):
                break
            if max(abs(v) for v in dx) < 1e-14 * (1 + max(abs(v) for v in x)):
                ok = True
                break
        if not ok:
            continue
        Jv = _jac(dlaws, qs, unknowns, x, params_mid)
        Yf = _inv(Jv) if Jv else None
        if Yf is None:
            continue
        for e in (radii or (20, 16, 12, 8, 6, 4)):
            cert = {"centre": [str(F(v).limit_denominator(1 << 60)) for v in x], "radius": str(F(1, 1 << e)),
                    "Y": [[str(F(v).limit_denominator(1 << 40)) for v in row] for row in Yf],
                    "Z": [[str(F(v).limit_denominator(1 << 40)) for v in row] for row in Jv]}
            res = check(laws, unknowns, qs, cert)
            if res[0]:
                return cert, res
    return None


def _excluded(laws, qs, box):
    """Some law's reading over the box (× the parameter box) excludes 0."""
    for g in laws:
        r = _rd(g, qs, box)
        if r == "never" or (r is not None and (r[0] > 0 or r[1] < 0)):
            return True
    return False


def _cube_of(cert, unknowns):
    c = [F(v) for v in cert["centre"]]
    r = F(cert["radius"])
    return {n: (c[i] - r, c[i] + r) for i, n in enumerate(unknowns)}


def _inside(box, cube):
    return all(cube[n][0] <= box[n][0] and box[n][1] <= cube[n][1] for n in box)


def _meets(cube, region):
    return all(cube[n][0] <= region[n][1] and region[n][0] <= cube[n][1] for n in region)


def _in_region(sols, unknowns, region):
    """Only the solutions whose cube meets the region, in the order of their centres. Found by the curator's
    shakedown, 2026-11-08: cos x = 0.99 in [-100, 100] was answered "64 solutions" — 62 are there; Newton from a box
    at the edge walked out and certified the true roots ±119.52 OUTSIDE the region (a cube outside covers no box of
    the region, so the exhaustion was right; the LIST was not)."""
    keep = [(c, h) for c, h in sols if _meets(_cube_of(c, unknowns), region)]
    return sorted(keep, key=lambda ch: [F(v) for v in ch[0]["centre"]])


def solve_all(laws, unknowns, qs, region, budget=6000):
    """B (the curator's "Делай Б", 2026-11-08): ALL the solutions in the search region. The region is split into
    boxes; each box is EXCLUDED (some law's reading there excludes 0, for every parameter in the box) or lies inside
    the cube of a CERTIFIED solution (unique there, `check`), or is split again. When nothing is left the answer is
    complete: every solution in the region is one of the certified ones (each unique in its cube; a cube may reach
    out of the region). Returns {"complete": bool, "solutions": [(cert, how)], "boxes": n}."""
    region = {n: (F(region[n][0]), F(region[n][1])) for n in unknowns}
    sols, cubes = [], []
    todo, seen = [region], 0
    while todo:
        box = todo.pop()
        seen += 1
        if seen > budget:
            return {"complete": False, "solutions": _in_region(sols, unknowns, region), "boxes": seen}
        if _excluded(laws, qs, box):
            continue
        if any(_inside(box, c) for c in cubes):
            continue
        guess = [float((box[n][0] + box[n][1]) / 2) for n in unknowns]
        found = search(laws, unknowns, qs, guesses=[guess], radii=(4, 6, 8, 10, 12, 14, 16, 18, 20))
        if found is not None:
            cert, how = found
            c = [F(v) for v in cert["centre"]]
            if not any(all(cb[n][0] <= c[i] <= cb[n][1] for i, n in enumerate(unknowns)) for cb in cubes):
                sols.append((cert, how[1]))
                cubes.append(_cube_of(cert, unknowns))
            if any(_inside(box, cb) for cb in cubes):
                continue
        n = max(unknowns, key=lambda m: box[m][1] - box[m][0])
        lo, hi = box[n]
        if hi - lo <= F(1, 1 << 60):
            return {"complete": False, "solutions": _in_region(sols, unknowns, region), "boxes": seen}
        mid = (lo + hi) / 2
        todo.append(dict(box, **{n: (lo, mid)}))
        todo.append(dict(box, **{n: (mid, hi)}))
    # the cubes that EXHAUST the region are as large as the check allows; the ANSWER is each solution in the
    # smallest cube the check accepts (a sub-cube of a cube with one solution has that one solution only)
    fine = []
    for cert, how in sols:
        g = [float(F(v)) for v in cert["centre"]]
        f2 = search(laws, unknowns, qs, guesses=[g], radii=(20, 16, 12, 8))
        if f2 is not None and _inside(_cube_of(f2[0], unknowns), _cube_of(cert, unknowns)):
            fine.append((f2[0], f2[1][1]))
        else:
            fine.append((cert, how))
    return {"complete": True, "solutions": _in_region(fine, unknowns, region), "boxes": seen}
