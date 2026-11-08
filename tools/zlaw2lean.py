"""zlaw2lean — an implicit law with exp / ln / log10 / division / powers and REAL PARAMETERS, as a Lean theorem on VR's
continuum (lean/ZRootPar.lean, `par_root`).

    python3 tools/zlaw2lean.py pump      (the pump of test_implicit.py: Swamee-Jain friction, 8 parameters)

The law g(q, p) = 0 is read by znumjudge._parse_arith (the same reader zimplicit uses) and translated, node for node,
into ZXE.XE:
  * a rational constant: a dyadic `.cst`, or `.div (.cst num) (.cst den)`;
  * `pow(y, k)`, k a natural number: `.pow y k`; `pow(y, r)`, r not natural: `exp(r·ln y)`;
  * `log10 y = ln y / ln 10`; `exp`, `ln` as they are.
No algebra is done here (the translation is the tree), so NOTHING is trusted beyond the reader: every reading — signs,
slopes in q, the Lipschitz reading in the parameters, the positivity of every denominator and ln argument — is
computed and checked by the Lean kernel (`decide +kernel` on `chkP`).

The parameters: variable 0 is q, the parameters are variables 1, 2, … in sorted order. Each sits on an OUTER dyadic
interval `[lo − 2^-μ, hi + 2^-μ]` (rounded outward), so the user's box is inside the INNER box of `InnerIn μ`. The
theorem: for EVERY real parameter vector in the inner box, the law has a root in [a, b], and only one.

Said, not hidden: that the user's decimal box is inside the inner box is Python's Fractions here.
"""
import math, os, subprocess, sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
LEAN = os.path.join(ROOT, "lean")
sys.path.insert(0, ROOT)

MU = 80      # the margin 2^-MU between the user's box and the outer box
KD = 96      # dyadic precision of the outer box ends


def dy(q):
    q = F(q); e = q.denominator.bit_length() - 1
    assert q.denominator == 1 << e, q
    m = q.numerator
    return f"(⟨⟨{max(m, 0)}, {max(-m, 0)}⟩, {e}⟩ : D)"


def is_dyadic(q):
    q = F(q)
    return q.denominator & (q.denominator - 1) == 0


def floor_dy(x, k):
    return F(math.floor(F(x) * (1 << k)), 1 << k)


def ceil_dy(x, k):
    return F(math.ceil(F(x) * (1 << k)), 1 << k)


def cst(q):
    q = F(q)
    if is_dyadic(q):
        return f"(.cst {dy(q)})"
    return f"(.div (.cst {dy(q.numerator)}) (.cst {dy(q.denominator)}))"


def to_xe(node, idx):
    if isinstance(node, F):
        return cst(node)
    if isinstance(node, int):
        return cst(F(node))
    if isinstance(node, str):
        return f"(.var {idx[node]})"
    op = node[0]
    if op in ("add", "sub", "mul", "div"):
        return f"(.{op} {to_xe(node[1], idx)} {to_xe(node[2], idx)})"
    if op == "pow":
        base, k = node[1], node[2]
        if isinstance(k, F) and k.denominator == 1 and k >= 0:
            return f"(.pow {to_xe(base, idx)} {k.numerator})"
        return f"(.exp (.mul {to_xe(k, idx)} (.ln {to_xe(base, idx)})))"
    if op == "log10":
        return f"(.div (.ln {to_xe(node[1], idx)}) (.ln {cst(10)}))"
    if op in ("exp", "ln"):
        return f"(.{op} {to_xe(node[1], idx)})"
    raise ValueError(f"not translated (yet): {op}")


def law_xe(g, q, qs):
    names = sorted(n for n in qs if n != q)
    idx = {q: 0, **{n: i + 1 for i, n in enumerate(names)}}
    return to_xe(g, idx), names, idx


def ps_text(names, idx, qs):
    rows = []
    for n in names:
        lo, hi = F(qs[n]["lo"]), F(qs[n]["hi"])
        olo = floor_dy(lo - F(1, 1 << MU), KD)
        ohi = ceil_dy(hi + F(1, 1 << MU), KD)
        assert olo + F(1, 1 << MU) <= lo and hi <= ohi - F(1, 1 << MU)
        rows.append(f"({idx[n]}, ({dy(olo)}, {dy(ohi)}), (⟨⟨0, 0⟩, 0⟩ : D))")
    return "[" + ", ".join(rows) + "]"


HEADER = "import ZRootPar\nopen ZNumBin ZIv ZXE ZRootExp ZRootDiv ZRootPVR ZRootPar\n"


def lean_run(text, name):
    os.makedirs(os.path.join(LEAN, "gen"), exist_ok=True)
    path = os.path.join(LEAN, "gen", name)
    with open(path, "w") as f:
        f.write(text)
    r = subprocess.run(["lake", "env", "lean", path], cwd=LEAN, capture_output=True, text=True, timeout=3000)
    return r.stdout + r.stderr


def probe(xe, ps, a, b, neg):
    e = f"(.sub (.cst (⟨⟨0, 0⟩, 0⟩ : D)) {xe})" if neg else xe
    t = HEADER + f"def E : XE := {e}\ndef P : PS := {ps}\ndef A : D := {dy(a)}\ndef B : D := {dy(b)}\n"
    t += "#eval posOK (BoxOf A B P) E\n"
    t += "#eval (slX (BoxOf A B P) Vx E)\n"
    t += "#eval (slX (BoxOf A B P) Vp E)\n"
    t += "#eval (ivX (BoxOf A A P) E)\n"
    t += "#eval (ivX (BoxOf B B P) E)\n"
    return e, lean_run(DTO + t, "LawProbe.lean")


DTO = ""


def read_ds(text):
    """The dyadics printed by #eval, as Fractions (display and choice of constants only; the kernel decides)."""
    import re
    out = []
    for p, n, e in re.findall(r"p := (\d+), n := (\d+) \}, e := (\d+)", text):
        out.append(F(int(p) - int(n), 1 << int(e)))
    return out


LAWS = {
    "pump": dict(
        q="Q", a=F(5, 1000), b=F(65, 10000),
        qt=("H0=[38,42] credit, a=[9000,11000] credit, z=[14.5,15.5] credit, L=[118,122] credit, "
            "D=[0.0495,0.0505] credit, Km=[4.5,5.5] credit, eps=[0.000045,0.000055] credit, "
            "nu=[0.00000095,0.00000105] credit, pi=[3.14159265358979,3.14159265358980] credit, "
            "g0=[9.80665,9.80665] credit, Q=? credit"),
        ex=("H0 - a*Q*Q - z - (0.25/pow(log10(eps/(3.7*D) + 5.74/pow(4*Q/(pi*D*nu), 0.9)), 2)*L/D + Km)"
            "*8*Q*Q/(pi*pi*g0*pow(D, 4))")),
    "oil": dict(
        q="Tho", a=F(30), b=F(70),
        qt=("mh=[97/50,103/50] credit, Thi=[93,97] credit, mc=[38/25,42/25] credit, Tci=[15,28] credit, "
            "Rf=[1/10000,6/10000] credit, Tho=? credit"),
        ex=("Thi - Tho - (1 - exp(0 - (1/(1/(1050*pow((Thi + Tho)/160, 0.8)*pow(mh/2, 0.5)) + Rf)*7/(mh*2100))"
            "*(1 - mh*2100/(mc*4180))))/(1 - mh*2100/(mc*4180)*exp(0 - (1/(1/(1050*pow((Thi + Tho)/160, 0.8)"
            "*pow(mh/2, 0.5)) + Rf)*7/(mh*2100))*(1 - mh*2100/(mc*4180))))*(mh*2100/(mh*2100))*(Thi - Tci)"),
        tree=[("mh", 4), ("mc", 4)], consts=(2, 2, 6, 18),
        title="THE OIL COOLER of the blind test (b02, c01)",
        doc="Thi − Tho − ε(Tho)·(Thi − Tci) = 0 (the ε-NTU law, h ∝ ((Thi + Tho)/160)^0.8·(mh/2)^0.5)"),
}

W_OVERLAP = F(1, 1 << 70)


def tree_text(splits, idx, qs, level=0):
    if level == len(splits):
        return ".leaf"
    name, k = splits[level]
    lo, hi = F(qs[name]["lo"]), F(qs[name]["hi"])

    def rng(i0, i1):
        if i1 - i0 == 1:
            return tree_text(splits, idx, qs, level + 1)
        mid = (i0 + i1) // 2
        c = floor_dy(lo + (hi - lo) * mid / k, KD)
        return f"(.cut {idx[name]} {dy(c)} {dy(W_OVERLAP)} {rng(i0, mid)} {rng(mid, i1)})"
    return rng(0, k)


def main():
    import znumjudge as ZJ
    which = sys.argv[1] if len(sys.argv) > 1 else "pump"
    spec = LAWS[which]
    qs = ZJ.parse_quantities(spec["qt"])[0]
    g = ZJ._parse_arith(spec["ex"], qs)
    xe, names, idx = law_xe(g, spec["q"], qs)
    ps = ps_text(names, idx, qs)
    a, b = floor_dy(spec["a"], 20), ceil_dy(spec["b"], 20)
    print(names)
    if "tree" in spec:
        return emit_tree(which, spec, xe, names, idx, qs, ps, a, b)
    neg = len(sys.argv) <= 2 or sys.argv[2] != "pos"
    e, out = probe(xe, ps, a, b, neg=neg)
    print(out[:2500])
    vals = read_ds(out)
    print([float(x) for x in vals])
    assert out.split("\n")[0].strip() == "true", out[:500]
    k_lo, k_hi, p_lo, p_hi, fa_lo, fa_hi, fb_lo, fb_hi = vals
    assert k_lo > 0 and fa_hi <= 0 and fb_lo >= 0, "the readings do not certify a root on [a, b]"
    s_ = 0
    while F(1, 1 << s_) > k_lo:
        s_ += 1
    C = max(0, math.ceil(math.log2(float(k_hi))) + 1)
    L = max(0, math.ceil(math.log2(max(abs(float(p_lo)), abs(float(p_hi)), 1))) + 1)
    B = max(0, math.ceil(math.log2(float(b - a))) + 1) if b > a else 0
    order = ", ".join(f"{n} = var {idx[n]}" for n in names)
    text = f"""import ZRootPar
/-!
# ZPumpRoot — THE PUMP of the blind test (b03), as a theorem on VR's continuum. Zero axioms. GENERATED by
`tools/zlaw2lean.py pump` from the law as the user wrote it (the zimplicit stand `test_implicit.py`, part 2):

    H0 − a·Q² − z − (0.25 / log10(eps/(3.7·D) + 5.74 / (4Q/(π·D·ν))^0.9)² · L/D + Km) · 8Q² / (π²·g0·D⁴) = 0

(Swamee–Jain friction coupled to the flow; `log10 y = ln y / ln 10`, `y^0.9 = exp(0.9·ln y)`). The law is read
NEGATED (`0 − g`, increasing in Q). Variables: Q = var 0, {order}.

**For EVERY real parameter vector in the inner box** (each parameter `2⁻⁸⁰` inside its outer interval — the user's
box is inside it), the pump has an operating point Q in [{float(a):.6f}, {float(b):.6f}] m³/s, and only one. The
kernel checked: every denominator and `ln` argument reads `≥ 2⁻⁶⁴`; the slope in Q reads in
[{float(k_lo):.0f}, {float(k_hi):.0f}]; the slope in the parameters in ±{float(p_hi):.3g}; the signs at the ends.
-/

namespace ZPumpRoot
open ZNumBin ZIv ZXE ZRootExp ZRootDiv ZRootPVR ZRootPar VR.Numbers ZRealCF

/-- The pump law, negated: `0 − g(Q, p)`. -/
def pumpE : XE := {e}
/-- The parameters on their outer intervals. -/
def pumpPS : PS := {ps}
def qa : D := {dy(a)}
def qb : D := {dy(b)}

/-- **THE PUMP'S OPERATING POINT EXISTS AND IS UNIQUE**, for every real parameter vector in the inner box. -/
theorem pump_root (p : Nat → RExpr) (hin : InnerIn {MU} p pumpPS) :
    ∃ x : RExpr, (rle (dv rOH qa) x ∧ rle x (dv rOH qb)) ∧ rEq (FP pumpE qa pumpPS p x) rzero ∧
      ∀ y, rle (dv rOH qa) y → rle y (dv rOH qb) → rEq (FP pumpE qa pumpPS p y) rzero → rEq y x :=
  par_root pumpE qa qb pumpPS {s_} {C} {B} {L} (by decide +kernel) p hin

/-- The fork's other side: on [0.001, 0.004] (below every operating point) the right end is not read positive —
the certificate is refused. -/
example : chkP pumpE {dy(floor_dy(F(1, 1000), 20))} {dy(ceil_dy(F(4, 1000), 20))} pumpPS {s_} {C} {B} {L} = false := by decide +kernel

end ZPumpRoot

#print axioms ZPumpRoot.pump_root
"""
    with open(os.path.join(LEAN, "ZPumpRoot.lean"), "w") as f:
        f.write(text)
    print("constants s C B L =", s_, C, B, L)


def emit_tree(which, spec, xe, names, idx, qs, ps, a, b):
    e = f"(.sub (.cst (⟨⟨0, 0⟩, 0⟩ : D)) {xe})"
    s_, C, B, L = spec["consts"]
    tree = tree_text(spec["tree"], idx, qs)
    order = ", ".join(f"{n} = var {idx[n]}" for n in names)
    nm = "Z" + which.capitalize() + "Root"
    leaves = 1
    for _, k in spec["tree"]:
        leaves *= k
    text = f"""import ZRootPar
/-!
# {nm} — {spec["title"]}, as a theorem on VR's continuum. Zero axioms. GENERATED by `tools/zlaw2lean.py {which}`
from the law as the user wrote it:

    {spec["doc"]}

read NEGATED (`0 − g`, increasing in {spec["q"]}). Variables: {spec["q"]} = var 0, {order}.

The parameter box is too wide for one reading to decide the end signs (dependency), so it is COVERED by a tree of cuts
({" × ".join(f"{n}: {k}" for n, k in spec["tree"])} = {leaves} boxes, overlap 2⁻⁷⁰); each box passes `chkP`, and a real parameter is
placed in a box by cotransitivity, not by a decision (`ZRootPar.tree_root`).

**For EVERY real parameter vector in the inner box** (each parameter `2⁻⁸⁰` inside its outer interval — the user's box is
inside it), {spec["q"]} has one root in [{float(a):g}, {float(b):g}], and only one.
-/

namespace {nm}
open ZNumBin ZIv ZXE ZRootExp ZRootDiv ZRootPVR ZRootPar VR.Numbers ZRealCF

/-- The law, negated. -/
def lawE : XE := {e}
def lawPS : PS := {ps}
def lawT : PT := {tree}
def qa : D := {dy(a)}
def qb : D := {dy(b)}

/-- **THE ROOT EXISTS AND IS UNIQUE**, for every real parameter vector in the inner box. -/
theorem law_root (p : Nat → RExpr) (hin : InnerIn {MU} p lawPS) :
    ∃ x : RExpr, (rle (dv rOH qa) x ∧ rle x (dv rOH qb)) ∧ rEq (FP lawE qa lawPS p x) rzero ∧
      ∀ y, rle (dv rOH qa) y → rle y (dv rOH qb) → rEq (FP lawE qa lawPS p y) rzero → rEq y x :=
  tree_root lawE qa qb {s_} {C} {B} {L} {MU} lawT lawPS (by decide +kernel) p hin

/-- Without the cover the readings do not decide: the single box is refused. -/
example : chkP lawE qa qb lawPS {s_} {C} {B} {L} = false := by decide +kernel

end {nm}

#print axioms {nm}.law_root
"""
    with open(os.path.join(LEAN, nm + ".lean"), "w") as f:
        f.write(text)
    print("wrote", nm)


if __name__ == "__main__":
    main()
