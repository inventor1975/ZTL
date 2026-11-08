"""zkraw2lean — a SYSTEM of laws F(x) = 0 (exp / ln / log10 / atan / sin / cos / division / powers) as a Lean theorem on VR's continuum:
a solution in a cube, and only one there (lean/ZKrawSys.lean, `sys_root`).

    python3 tools/zkraw2lean.py circle_exp      (writes lean/ZSysCircleExp.lean)
    python3 tools/zkraw2lean.py chem3
    python3 tools/zkraw2lean.py chem3p          (with real parameters a, b on intervals)

Untrusted search, checked result. Python only PROPOSES: Newton in floats for the centre y, the preconditioner
Y ≈ J(y)⁻¹, the matrix Z ≈ J(y), the cube radius r. Lean's kernel CHECKS (`decide +kernel`):
  chkK — for G(x) = x − Y·F(x): every denominator / ln argument reads ≥ 2⁻⁶⁴ on the cube; each row of the staircase
         slope readings sums to ≤ ½ (contraction); G(centre) ± r/2 lies in the cube shrunk by 2⁻ᴿ (into);
  chkZ — every row of |I − Z·Y| (exact dyadic arithmetic) sums to ≤ ½ (Y invertible).
The laws are read by znumjudge._parse_arith and translated node for node (tools/zlaw2lean.py).
"""
import math, os, sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
LEAN = os.path.join(ROOT, "lean")
sys.path.insert(0, ROOT); sys.path.insert(0, HERE)
import zlaw2lean as Z  # noqa: E402

SYSTEMS = {
    "circle_exp": dict(vars=["x", "y"], laws=["x*x + y*y - 1", "x - exp(y)"], guess=[0.5, -0.5],
                       title="the circle meets the exponential: x² + y² = 1, x = eʸ"),
    "chem3": dict(vars=["x", "y", "z"], laws=["x + y + z - 3", "x*exp(y) - 2", "ln(z) + x*y - 1/2"],
                  guess=[1.0, 0.5, 1.5], title="a 3×3 system with exp and ln: x + y + z = 3, x·eʸ = 2, ln z + x·y = ½"),
    "chem3p": dict(vars=["x", "y", "z"], laws=["x + y + z - 3", "x*exp(y) - a", "ln(z) + x*y - b"],
                   params={"a": ("1.95", "2.05"), "b": ("0.45", "0.55")}, guess=[1.6, 0.2, 1.2],
                   title="the 3×3 system with REAL PARAMETERS: x + y + z = 3, x·eʸ = a, ln z + x·y = b, "
                         "a ∈ [1.95, 2.05], b ∈ [0.45, 0.55]", cover={"a": 5, "b": 5}),
}


def fl(node, env):
    if isinstance(node, (F, int)):
        return float(node)
    if isinstance(node, str):
        return env[node]
    op = node[0]
    a = fl(node[1], env)
    if op == "log10":
        return math.log10(a)
    if op == "exp":
        return math.exp(a)
    if op == "ln":
        return math.log(a)
    if op == "atan":
        return math.atan(a)
    if op == "sin":
        return math.sin(a)
    if op == "cos":
        return math.cos(a)
    if op == "tan":
        return math.tan(a)
    b = fl(node[2], env)
    if op == "min":
        return min(a, b)
    if op == "max":
        return max(a, b)
    if op == "add":
        return a + b
    if op == "sub":
        return a - b
    if op == "mul":
        return a * b
    if op == "div":
        return a / b
    if op == "pow":
        return a ** b
    raise ValueError(op)


def solve(A, b):
    n = len(A); M = [row[:] + [b[i]] for i, row in enumerate(A)]
    for c in range(n):
        p = max(range(c, n), key=lambda r: abs(M[r][c])); M[c], M[p] = M[p], M[c]
        for r in range(n):
            if r != c:
                f = M[r][c] / M[c][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [M[i][n] / M[i][i] for i in range(n)]


def inv(A):
    n = len(A)
    cols = [solve(A, [1.0 if i == j else 0.0 for i in range(n)]) for j in range(n)]
    return [[cols[j][i] for j in range(n)] for i in range(n)]


def lst(xs):
    return "[" + ", ".join(xs) + "]"


class NoVerdict(Exception):
    pass


def build(name, spec, out_dir=LEAN, nm=None, ex_force=None):
    """Write the Lean module for the system; returns (module name, path). Raises NoVerdict (Newton found no simple
    solution) or ValueError (a law not translated)."""
    import itertools
    import znumjudge as ZJ
    vs = spec["vars"]; d = len(vs)
    pars = spec.get("params", {})
    qt = ", ".join([f"{v}=? credit" for v in vs] + [f"{n}=[{lo},{hi}] credit" for n, (lo, hi) in pars.items()])
    qs = ZJ.parse_quantities(qt)[0]
    trees = [ZJ._parse_arith(t, qs) for t in spec["laws"]]
    pnames = sorted(pars)
    idx = {v: i for i, v in enumerate(vs)}
    idx.update({n: d + i for i, n in enumerate(pnames)})
    Fs = [Z.to_xe(t, idx) for t in trees]
    ps = Z.ps_text(pnames, idx, qs) if pnames else "[]"
    mid = {n: (float(F(qs[n]["lo"])) + float(F(qs[n]["hi"]))) / 2 for n in pnames}

    def Fn(x, pv):
        env = dict(zip(vs, x)); env.update(pv)
        return [fl(t, env) for t in trees]

    def J(x, pv, h=1e-7):
        cols = []
        for jj in range(d):
            xp = x[:]; xm = x[:]; xp[jj] += h; xm[jj] -= h
            fp, fm = Fn(xp, pv), Fn(xm, pv)
            cols.append([(a - b) / (2 * h) for a, b in zip(fp, fm)])
        return [[cols[jj][ii] for jj in range(d)] for ii in range(d)]

    def newton(x, pv):
        x = list(x)
        for _ in range(60):
            dx = solve(J(x, pv), Fn(x, pv))
            x = [a - b for a, b in zip(x, dx)]
        return x
    try:
        x = newton(spec["guess"], mid)
        res = max(abs(v) for v in Fn(x, mid))
    except (ValueError, ZeroDivisionError, OverflowError) as ex:
        raise NoVerdict(f"Newton failed: {ex}")
    if not (res < 1e-9):
        raise NoVerdict(f"Newton did not converge (residual {res})")
    print("root", x, "residual", res)
    shift = 0.0
    for corner in itertools.product(*[(float(F(qs[n]["lo"])), float(F(qs[n]["hi"]))) for n in pnames]):
        xc = newton(x, dict(zip(pnames, corner)))
        shift = max(shift, max(abs(a - b) for a, b in zip(xc, x)))
    ex = min(20, math.floor(-math.log2(4 * shift))) if shift > 0 else 20
    if ex_force is not None:
        ex = min(ex, ex_force)
    r, rh = F(1, 1 << ex), F(1, 1 << (ex + 1))
    R, L = 40, 60
    E = max(0, math.ceil(math.log2(float(2 * r))))
    print("parameter shift", shift, "cube radius 2^-%d" % ex)
    if "cover" in spec:
        return emit_cover(name, spec, vs, d, pnames, idx, qs, Fs, ps, newton, J, x, Fn, out_dir, nm)
    Jx = J(x, mid); Yf = inv(Jx)
    ys = [Z.floor_dy(F(v), 48) for v in x]
    Yd = [[Z.floor_dy(F(v), 30) for v in row] for row in Yf]
    Zd = [[Z.floor_dy(F(v), 30) for v in row] for row in Jx]
    nm = nm or "ZSys" + "".join(q.capitalize() for q in name.split("_"))
    vnames = ", ".join([f"{v} = var {i}" for i, v in enumerate(vs)] + [f"{n} = var {idx[n]}" for n in pnames])
    laws = "\n".join(f"    {t} = 0" for t in spec["laws"])
    pdoc = ("**for EVERY real parameter vector in the inner box** (each parameter 2⁻⁸⁰ inside its outer interval; the "
            "box: " + ", ".join(f"{n} ∈ [{lo}, {hi}]" for n, (lo, hi) in pars.items()) + ")") if pnames else "(no parameters)"
    away = [Z.dy(v + 4 * r) for v in ys]
    text = f"""import ZKrawSys
/-!
# {nm} — {spec["title"]}: a solution on VR's continuum, and only one in its cube. Zero axioms. GENERATED by
`tools/zkraw2lean.py {name}`:

{laws}

Variables: {vnames}. The cube: centre ≈ ({", ".join(f"{v:.12g}" for v in x)}), radius 2⁻{ex}; {pdoc}. The kernel
checks the Krawczyk certificate for `G = x − Y·F` and the invertibility of `Y` (`ZKrawSys.sys_root`).
-/

namespace {nm}
open ZNumBin ZIv ZXE ZRootExp ZRootDiv ZRootPVR ZKraw ZKrawSys VR.Numbers ZRealCF

def Fs : Nat → XE := nthX {lst(Fs)}
def ys : List D := {lst([Z.dy(v) for v in ys])}
def PS0 : PS := {ps}
def Y : Nat → Nat → D := mat {lst([lst([Z.dy(v) for v in row]) for row in Yd])}
def Zm : Nat → Nat → D := mat {lst([lst([Z.dy(v) for v in row]) for row in Zd])}

/-- **THE SYSTEM HAS ITS SOLUTION, AND ONLY ONE IN THE CUBE**{", for every real parameter vector in the inner box" if pnames else ""}. -/
theorem solution (p : ZBanach.Vec) (hin : InnerIn {Z.MU} p PS0) :
    ∃ x : ZBanach.Vec, InC {d} ys {Z.dy(r)} x ∧ (∀ i, i < {d} → rEq (evR (envK {d} (peOf PS0 p) x) (Fs i)) rzero) ∧
      ∀ u, InC {d} ys {Z.dy(r)} u → (∀ i, i < {d} → rEq (evR (envK {d} (peOf PS0 p) u) (Fs i)) rzero) →
        ∀ i, i < {d} → rEq (u i) (x i) :=
  sys_root (d := {d}) (Y := Y) (Fs := Fs) (ys := ys) (r := {Z.dy(r)}) (rh := {Z.dy(rh)}) (R := {R}) (E := {E}) (L := {L})
    (ps := PS0) (Z := Zm) (by decide +kernel) (by decide +kernel) p hin

/-- The fork's other side: a cube displaced by 4r (no solution inside) is refused. -/
example : chkK {d} {lst(away)} {Z.dy(r)} {Z.dy(rh)} {R} {E} {L} PS0 (Gsys {d} Y Fs) = false := by decide +kernel

end {nm}

#print axioms {nm}.solution
"""
    path = os.path.join(out_dir, nm + ".lean")
    with open(path, "w") as f:
        f.write(text)
    print("wrote", nm)
    return nm, path


W_OVERLAP = F(1, 1 << 70)


def emit_cover(name, spec, vs, d, pnames, idx, qs, Fs, ps, newton, J, x0, Fn, out_dir=LEAN, nm=None):
    import itertools
    MU = Z.MU
    outer = {}
    for n in pnames:
        lo, hi = F(qs[n]["lo"]), F(qs[n]["hi"])
        outer[n] = (Z.floor_dy(lo - F(1, 1 << MU), Z.KD), Z.ceil_dy(hi + F(1, 1 << MU), Z.KD))
    R, L = 40, 60
    leaves = []
    leaf_texts = []

    def leaf(box):
        midp = {n: float((box[n][0] + box[n][1]) / 2) for n in pnames}
        xc = newton(x0, midp)
        shift = 0.0
        for corner in itertools.product(*[(float(box[n][0]), float(box[n][1])) for n in pnames]):
            xs = newton(xc, dict(zip(pnames, corner)))
            shift = max(shift, max(abs(a - b) for a, b in zip(xs, xc)))
        ex = min(20, math.floor(-math.log2(4 * shift))) if shift > 0 else 20
    if ex_force is not None:
        ex = min(ex, ex_force)
        r, rh = F(1, 1 << ex), F(1, 1 << (ex + 1))
        Jx = J(xc, midp); Yf = inv(Jx)
        ys = [Z.floor_dy(F(v), 48) for v in xc]
        Yd = [[Z.floor_dy(F(v), 30) for v in row] for row in Yf]
        Zd = [[Z.floor_dy(F(v), 30) for v in row] for row in Jx]
        leaves.append((ys, r))
        leaf_texts.append(f"(.leaf {lst([Z.dy(v) for v in ys])} {Z.dy(r)} {Z.dy(rh)} "
                          f"{lst([lst([Z.dy(v) for v in row]) for row in Yd])} {lst([lst([Z.dy(v) for v in row]) for row in Zd])})")
        return (f"(.leaf {lst([Z.dy(v) for v in ys])} {Z.dy(r)} {Z.dy(rh)} "
                f"{lst([lst([Z.dy(v) for v in row]) for row in Yd])} {lst([lst([Z.dy(v) for v in row]) for row in Zd])})")

    order = list(spec["cover"].items())

    def build(level, box):
        if level == len(order):
            return leaf(box)
        n, k = order[level]
        lo0, hi0 = F(qs[n]["lo"]), F(qs[n]["hi"])

        def rng(i0, i1, bx):
            if i1 - i0 == 1:
                return build(level + 1, bx)
            m = (i0 + i1) // 2
            c = Z.floor_dy(lo0 + (hi0 - lo0) * m / k, Z.KD)
            left = dict(bx); left[n] = (bx[n][0], c + W_OVERLAP)
            right = dict(bx); right[n] = (c - W_OVERLAP, bx[n][1])
            return f"(.cut {idx[n]} {Z.dy(c)} {Z.dy(W_OVERLAP)} {rng(i0, m, left)} {rng(m, i1, right)})"
        return rng(0, k, box)
    tree = build(0, dict(outer))
    los = [min(ys[i] - r for ys, r in leaves) for i in range(d)]
    his = [max(ys[i] + r for ys, r in leaves) for i in range(d)]
    ys0 = [Z.floor_dy((a + b) / 2, 48) for a, b in zip(los, his)]
    half = max(max(ys0[i] - los[i], his[i] - ys0[i]) for i in range(d))
    e0 = math.floor(-math.log2(float(half)))
    r0 = F(1, 1 << e0) if F(1, 1 << e0) >= half else F(2, 1 << e0)
    while r0 < half:
        r0 *= 2
    E = max(0, math.ceil(math.log2(float(2 * max(r for _, r in leaves) ))) + 1)
    nm = nm or "ZSys" + "".join(q.capitalize() for q in name.split("_"))
    vnames = ", ".join([f"{v} = var {i}" for i, v in enumerate(vs)] + [f"{n} = var {idx[n]}" for n in pnames])
    laws = "\n".join(f"    {t} = 0" for t in spec["laws"])
    nleaf = len(leaves)
    pars = spec["params"]
    text = f"""import ZKrawCover
/-!
# {nm} — {spec["title"]}: a solution on VR's continuum for every real parameter vector, locally unique. Zero axioms.
GENERATED by `tools/zkraw2lean.py {name}`:

{laws}

Variables: {vnames}. The parameter box ({", ".join(f"{n} ∈ [{lo}, {hi}]" for n, (lo, hi) in pars.items())}) is
COVERED by {nleaf} leaves ({" × ".join(f"{n}: {k}" for n, k in order)}, overlap 2⁻⁷⁰); each leaf carries its own Krawczyk
certificate (centre by Newton at the leaf's middle, cube, `Y`, `Z`), all checked by the kernel (`ZKrawCover.kt_root`).
**For every real parameter vector in the inner box**: a solution in the bounding cube, unique in its leaf's cube.
-/

namespace {nm}
open ZNumBin ZIv ZXE ZRootExp ZRootDiv ZRootPVR ZKraw ZKrawSys ZKrawCover VR.Numbers ZRealCF

def Fs : Nat → XE := nthX {lst(Fs)}
def PS0 : PS := {ps}
def ys0 : List D := {lst([Z.dy(v) for v in ys0])}
def r0 : D := {Z.dy(r0)}
def T : KT := {tree}

/-- **THE SYSTEM HAS ITS SOLUTION FOR EVERY REAL PARAMETER VECTOR IN THE INNER BOX** — in the bounding cube, unique
in the cube of its leaf. -/
theorem solution (p : ZBanach.Vec) (hin : InnerIn {MU} p PS0) : Sol {d} Fs ys0 r0 PS0 p :=
  kt_root {d} Fs ys0 r0 {R} {E} {L} {MU} T PS0 (by decide +kernel) p hin

/-- Without the cover the readings do not decide: one leaf's certificate over the whole parameter box is refused. -/
example : chkKT {d} Fs ys0 r0 {R} {E} {L} {MU} PS0 {leaf_texts[0]} = false := by decide +kernel

end {nm}

#print axioms {nm}.solution
"""
    path = os.path.join(out_dir, nm + ".lean")
    with open(path, "w") as f:
        f.write(text)
    print("wrote", nm, "leaves", nleaf, "r0", float(r0), "leaf radii", sorted(set(float(r) for _, r in leaves)))
    return nm, path


def system_to_lean(spec, nm):
    """THE SYSTEM JUDGE: Python proposes (Newton, Y, Z, cube, cover), the Lean kernel disposes. Status: "theorem"
    (the kernel accepted: a solution in the cube, unique there — for every parameter vector in the inner box),
    "refused" (the kernel accepted none of the proposals — the cube radius is tried at 2⁻²⁰ (or the parameters'
    shift), then 2⁻¹⁶, 2⁻¹², 2⁻⁸, 2⁻⁶: a coarse reading, e.g. atan's value, needs a larger cube), "no verdict" (Newton found no simple solution), "not
    translated" (a function ZXE does not have)."""
    import subprocess
    gen = os.path.join(LEAN, "gen"); os.makedirs(gen, exist_ok=True)
    tried = []
    out, path = "", None
    for exf in (None, 16, 12, 8, 6):
        try:
            nm2, path = build(nm, spec, out_dir=gen, nm=nm, ex_force=exf)
        except NoVerdict as ex:
            return {"status": "no verdict", "why": str(ex)}
        except ValueError as ex:
            return {"status": "not translated", "why": str(ex)}
        r = subprocess.run(["lake", "env", "lean", path], cwd=LEAN, capture_output=True, text=True, timeout=3000)
        out = r.stdout + r.stderr
        tried.append(exf)
        if f"'{nm}.solution' does not depend on any axioms" in out and "error" not in out:
            return {"status": "theorem", "file": path, "radius_exp_cap": exf, "tried": tried}
    return {"status": "refused", "why": out[:400], "file": path, "tried": tried}


def main():
    name = sys.argv[1] if len(sys.argv) > 1 else "circle_exp"
    build(name, SYSTEMS[name])


if __name__ == "__main__":
    main()
