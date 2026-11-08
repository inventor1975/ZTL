"""zimplicit2lean — an implicit law's root as a Lean theorem on VR's continuum (lean/ZRootPVR.lean).

    python3 tools/zimplicit2lean.py   (the fan of test_implicit.py; see `fan()` for the call)

A RATIONAL law g(q, p) = 0 (here: divisions by positive parameters) is turned into an integer polynomial
f = M·L·g (M the product of the positive denominators, L the common denominator of the coefficients — both
positive on the box, so f and g have the same roots). Then:
  * [a, b] a dyadic bracket around zimplicit's hull; each parameter on a dyadic interval around its box, the
    user's box inside it by a margin 2^-mu;
  * Lean computes the interval readings (#eval) — the signs at a and b, the slope in q, the divided difference in
    each parameter; the constants of the certificate are read off them;
  * the theorem `∀ p, InnerIn mu p ps → ∃ root ∈ [a, b], f(root, p) = 0, unique` is emitted and checked by the
    kernel (RC by `decide +kernel`).
Untrusted: Lean decides. NOT checked in Lean (said, not hidden): that f = M·L·g with M, L > 0 on the box — that is
sympy's algebra here; and that the user's box is inside the inner region — Python's Fractions here.
"""
import math, os, re, subprocess, sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
LEAN = os.path.join(ROOT, "lean")
sys.path.insert(0, ROOT)
import sympy as sp


def to_sympy(node, sym):
    if isinstance(node, F):
        return sp.Rational(node.numerator, node.denominator)
    if isinstance(node, str):
        return sym[node]
    op = node[0]
    a, b = to_sympy(node[1], sym), to_sympy(node[2], sym)
    return {"add": a + b, "sub": a - b, "mul": a * b, "div": a / b}[op]


def dy(q):
    q = F(q); e = q.denominator.bit_length() - 1
    assert q.denominator == 1 << e, q
    m = q.numerator
    return f"⟨⟨{max(m, 0)}, {max(-m, 0)}⟩, {e}⟩"


def floor_dy(x, k):
    return F(math.floor(x * (1 << k)), 1 << k)


def ceil_dy(x, k):
    return F(math.ceil(x * (1 << k)), 1 << k)


def pe_of_poly(poly, gens, idx):
    terms = []
    for mon, c in poly.terms():
        c = int(c)
        t = f"(.cst {dy(F(c))})"
        for g, k in zip(gens, mon):
            if k:
                t = f"(.mul {t} (.pow (.var {idx[g]}) {k}))"
        terms.append(t)
    while len(terms) > 1:
        terms = [f"(.add {terms[i]} {terms[i + 1]})" if i + 1 < len(terms) else terms[i] for i in range(0, len(terms), 2)]
    return terms[0]


def lean(path):
    r = subprocess.run(["lake", "env", "lean", path], cwd=LEAN, capture_output=True, text=True, timeout=1800)
    return r.returncode, r.stdout + r.stderr


def parse_D(s):
    """`{ m := { p := P, n := N }, e := E }` -> Fraction"""
    m = re.findall(r"p := (\d+), n := (\d+) \}, e := (\d+)", s)
    return [F(int(p) - int(n), 1 << int(e)) for p, n, e in m]


def bridge(name, g, q, qs, hull, tag, search=None):
    params = sorted(n for n in qs if n != q and qs[n]["lo"] < qs[n]["hi"])
    sym = {n: sp.Symbol(n) for n in list(qs)}
    expr = sp.together(to_sympy(g, sym))
    num, den = sp.fraction(expr)
    # the denominator: a product of positive parameters and a positive constant
    for fac in sp.Mul.make_args(den):
        base = fac.as_base_exp()[0]
        if base.is_number:
            assert base > 0, fac
        else:
            assert str(base) in params and qs[str(base)]["lo"] > 0, f"denominator factor {fac} not a positive parameter"
    gens = [sym[q]] + [sym[n] for n in params]
    P = sp.Poly(sp.expand(num), *gens, domain="QQ")
    L = sp.ilcm(*[sp.Rational(c).q for c in P.coeffs()])
    P = sp.Poly(sp.expand(num * L), *gens, domain="ZZ")
    idx = {sym[q]: 0, **{sym[n]: i + 1 for i, n in enumerate(params)}}
    Y = len(params) + 1
    # bracket and boxes
    lo, hi = F(hull[0]), F(hull[1]); w = hi - lo
    k = 24
    brackets = [(floor_dy(lo - w / 4, k), ceil_dy(hi + w / 4, k)), (floor_dy(lo - w, k), ceil_dy(hi + w, k))]
    if search:
        brackets.append((floor_dy(F(search[0]), k), ceil_dy(F(search[1]), k)))
    mu, ps, inner = None, [], {}
    for n in params:
        pl, ph = qs[n]["lo"], qs[n]["hi"]; pw = ph - pl
        m = max(1, math.ceil(-math.log2(pw / 64)))
        ol, oh = floor_dy(pl - pw / 16, m + 2), ceil_dy(ph + pw / 16, m + 2)
        ps.append([n, ol, oh, None])
        mu = max(mu or 0, m + 4)
    for e in ps:
        assert e[1] + F(1, 1 << mu) <= qs[e[0]]["lo"] and qs[e[0]]["hi"] <= e[2] - F(1, 1 << mu), "user box not inside"
    def ps_text(Ls):
        return "[" + ", ".join(f"({i + 1}, ({dy(e[1])}, {dy(e[2])}), {dy(L_)})" for i, (e, L_) in enumerate(zip(ps, Ls))) + "]"
    head = ["import ZRootPVR", "open ZNumBin ZPoly ZIv ZRoot ZRootP ZRootPVR", "set_option maxRecDepth 100000", ""]
    last = None
    for (a, b) in brackets:
        for sign in (1, -1):
            f = pe_of_poly(sp.Poly(sign * P.as_expr(), *gens, domain="ZZ"), gens, idx)
            ps0 = ps_text([F(1)] * len(ps))
            probe = head + [f"def f : PE := {f}", f"def ps : PS := {ps0}",
                            f"#eval ivE (BoxOf {dy(a)} {dy(a)} ps) f", f"#eval ivE (BoxOf {dy(b)} {dy(b)} ps) f",
                            f"#eval ivE (ZRootP.BY (BoxOf {dy(a)} {dy(b)} ps) 0 {Y}) (ZRootP.ddv 0 {Y} f)"]
            probe += [f"#eval ivE (ZRootP.BY (BoxOf {dy(a)} {dy(b)} ps) {i + 1} {Y}) (ZRootP.ddv {i + 1} {Y} f)" for i in range(len(ps))]
            fn = os.path.join(LEAN, "gen", f"{tag}Probe.lean")
            os.makedirs(os.path.dirname(fn), exist_ok=True)
            open(fn, "w").write("\n".join(probe) + "\n")
            rc, out = lean(fn)
            vals = [parse_D(line) for line in out.splitlines() if line.startswith("some")]
            if len(vals) != 3 + len(ps):
                raise RuntimeError("probe failed: " + out[:600])
            (ka, kb, kx), kp = vals[:3], vals[3:]
            if kx[0] > 0:
                break
        else:
            raise RuntimeError(f"the slope in {q} has no strict sign over the box: {kx}")
        if not (ka[1] <= 0 and kb[0] >= 0):
            last = f"no sign change certified at [{float(a)}, {float(b)}]: f(a) in {ka}, f(b) in {kb}"
            continue
        last = None
        break
    if last:
        raise RuntimeError(last)
    s = max(0, math.floor(-math.log2(kx[0])))
    while F(1, 1 << s) > kx[0]:
        s += 1
    Lx = ceil_dy(kx[1], 4)
    Ls = [ceil_dy(max(abs(v[0]), abs(v[1])), 4) for v in kp]
    C = max(1, math.ceil(math.log2(max([Lx] + [sum(Ls)]) + 1)))
    B = max(0, math.ceil(math.log2(max(b - a, F(1)))))
    psT = ps_text(Ls)
    thm = head + [f"def f : PE := {f}", f"def ps : PS := {psT}", "",
        f"theorem cert : RC f {dy(a)} {dy(b)} ps {Y} {s} {C} {B} {dy(Lx)} where",
        "  hab := by decide +kernel", "  h0 := rfl", "  hY0 := rfl", "  hY := by decide +kernel"]
    for fld, box, cmp in (("ends_a", f"BoxOf {dy(a)} {dy(a)} ps", "dle K.2 dz"), ("ends_b", f"BoxOf {dy(b)} {dy(b)} ps", "dle dz K.1")):
        thm += [f"  {fld} := by",
                f"    obtain ⟨K, hK⟩ : ∃ K, ivE ({box}) f = some K := ⟨_, rfl⟩",
                f"    exact ⟨K, hK, by rw [show K = _ from (Option.some.inj hK).symm]; decide +kernel⟩"]
    thm += ["  slope := by",
            f"    obtain ⟨K, hK⟩ : ∃ K, ivE (ZRootP.BY (BoxOf {dy(a)} {dy(b)} ps) 0 {Y}) (ZRootP.ddv 0 {Y} f) = some K := ⟨_, rfl⟩",
            "    exact ⟨K, hK, by rw [show K = _ from (Option.some.inj hK).symm]; decide +kernel,",
            "      by rw [show K = _ from (Option.some.inj hK).symm]; decide +kernel⟩",
            "  lip := by decide +kernel", "  lsum := by decide +kernel", "  lx := by decide +kernel", "  wid := by decide +kernel", "",
            f"/-- **{name}**: for every VR parameter point strictly inside the box (margin 2^-{mu}), the law has a root in",
            f"`[{float(a):.6g}, {float(b):.6g}]`, and it is the only one there. (f = M·L·g, M, L > 0: Python's algebra.) -/",
            f"theorem law_root (p : Nat → VR.Numbers.RExpr) (hin : InnerIn {mu} p ps) :",
            f"    ∃ x, (VR.Numbers.rle (dv ZRealCF.rOH {dy(a)}) x ∧ VR.Numbers.rle x (dv ZRealCF.rOH {dy(b)})) ∧",
            f"      VR.Numbers.rEq (G f {dy(a)} ps p x) VR.Numbers.rzero ∧",
            f"      ∀ y, (VR.Numbers.rle (dv ZRealCF.rOH {dy(a)}) y ∧ VR.Numbers.rle y (dv ZRealCF.rOH {dy(b)})) →",
            f"        VR.Numbers.rEq (G f {dy(a)} ps p y) VR.Numbers.rzero → VR.Numbers.rEq x y :=",
            f"  ⟨root f _ _ ps p cert hin, root_in f _ _ ps p cert hin, root_is_root f _ _ ps p cert hin,",
            f"    fun y hy ry => root_unique f _ _ ps cert (parIn_inner p hin) (root_in f _ _ ps p cert hin) hy",
            f"      (root_is_root f _ _ ps p cert hin) ry⟩",
            "", "#print axioms law_root"]
    fn = os.path.join(LEAN, "gen", f"{tag}.lean")
    open(fn, "w").write("\n".join(thm) + "\n")
    rc, out = lean(fn)
    return rc, out, dict(a=a, b=b, s=s, C=C, B=B, Lx=Lx, Ls=Ls, mu=mu, slope=kx, ends=(ka, kb), sign=sign, file=fn)


def fan():
    from znumjudge import _parse_arith, parse_quantities
    import zimplicit as ZI
    qs = parse_quantities("pmax=[44.16,51.84] credit, Qmax=[0.038,0.042] credit, K=[27200,36800] credit, Q=? credit")[0]
    g = _parse_arith("pmax*(1 - Q/Qmax) - K*Q*Q", qs)
    cert = ZI.search_certificate(g, "Q", qs, ["0", "0.06"])
    ok, rng, how = ZI.check_implicit(g, "Q", qs, cert)
    assert ok, how
    return bridge("The fan's operating point", g, "Q", qs, rng, "ZImplicitFan", search=["0", "0.06"])


if __name__ == "__main__":
    rc, out, info = fan()
    print({k: (str(v) if not isinstance(v, (list, tuple)) else [str(x) for x in v]) for k, v in info.items()})
    print("lean exit", rc)
    print("\n".join(l for l in out.splitlines() if "axioms" in l or "error" in l)[:2000])
