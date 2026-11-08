"""zimplicit_lean — the judge's verdict on an implicit law becomes a Lean theorem, automatically.

    from tools.zimplicit_lean import verdict_to_lean
    st = verdict_to_lean(qtext, law, "Q", ["0.001", "0.06"], "MyLaw")

zimplicit (the judge) finds a certificate and checks it: "q has a unique root, in [lo, hi], over the box". This turns
that verdict into `∀ p in the inner box, ∃! q ∈ [a, b], g(q, p) = 0` on VR's continuum (lean/ZRootPar.lean):
  1. the law is translated node for node (tools/zlaw2lean.py: log10 = ln/ln10, y^r = exp(r·ln y));
  2. the bracket [a, b] is zimplicit's range widened by half its width (clipped to the user's search range);
  3. the orientation (g or −g) is the one whose slope reading is positive;
  4. if one box does not decide (the readings are too wide), a COVER is searched: the most sensitive parameters
     (by a float estimate at the ends) are split into k parts, k = 2, 3, 4, 6, 8, then pairs;
  5. the constants (s, C, B, L) are read off the readings; the kernel checks everything (`decide +kernel`).
Python proposes, Lean disposes: a wrong proposal is a refusal, never a theorem. Status values: "theorem", "refused"
(the kernel did not accept any proposal), "no verdict" (zimplicit gave no unique range), "not translated" (a function
ZXE does not have, e.g. min), with the reason.
"""
import itertools, math, os, re, subprocess, sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
LEAN = os.path.join(ROOT, "lean")
sys.path.insert(0, ROOT); sys.path.insert(0, HERE)
import zlaw2lean as Z  # noqa: E402

HEADER = "import ZRootPar\nopen ZNumBin ZIv ZXE ZRootExp ZRootDiv ZRootPVR ZRootPar\n"
CONSTS_CAP = 2000


def run_lean(text, name):
    os.makedirs(os.path.join(LEAN, "gen"), exist_ok=True)
    path = os.path.join(LEAN, "gen", name + ".lean")
    with open(path, "w") as f:
        f.write(text)
    r = subprocess.run(["lake", "env", "lean", path], cwd=LEAN, capture_output=True, text=True, timeout=3000)
    return r.stdout + r.stderr


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
    return {"add": lambda: a + b, "sub": lambda: a - b, "mul": lambda: a * b, "div": lambda: a / b,
            "pow": lambda: a ** b}[op]()


def leaf_boxes(splits, qs, outer):
    """The leaves of the cut tree, each as {name: (lo, hi)} (outer intervals, cuts with overlap)."""
    out = [dict(outer)]
    for n, k in splits:
        lo0, hi0 = F(qs[n]["lo"]), F(qs[n]["hi"])
        nxt = []
        for bx in out:
            def rng(i0, i1, b):
                if i1 - i0 == 1:
                    nxt.append(b); return
                m = (i0 + i1) // 2
                c = Z.floor_dy(lo0 + (hi0 - lo0) * m / k, Z.KD)
                left = dict(b); left[n] = (b[n][0], c + Z.W_OVERLAP_T)
                right = dict(b); right[n] = (c - Z.W_OVERLAP_T, b[n][1])
                rng(i0, m, left); rng(m, i1, right)
            rng(0, k, bx)
        out = nxt
    return out


Z.W_OVERLAP_T = F(1, 1 << 70)


def ps_of_box(names, idx, box):
    return "[" + ", ".join(f"({idx[n]}, ({Z.dy(box[n][0])}, {Z.dy(box[n][1])}), (⟨⟨0, 0⟩, 0⟩ : D))" for n in names) + "]"


def probe_leaves(e, names, idx, boxes, a, b, tag):
    """Lean's readings on every leaf box: slope in q, Lipschitz in the parameters, ends, posOK."""
    t = HEADER + f"def E : XE := {e}\ndef A : D := {Z.dy(a)}\ndef B : D := {Z.dy(b)}\n"
    for bx in boxes:
        P = ps_of_box(names, idx, bx)
        t += (f"#eval (posOK (BoxOf A B {P}) E, (slX (BoxOf A B {P}) Vx E), (slX (BoxOf A B {P}) Vp E), "
              f"(ivX (BoxOf A A {P}) E), (ivX (BoxOf B B {P}) E))\n")
    out = run_lean(t, "ZBridgeProbe_" + tag)
    rows = []
    for line in out.split("\n(") if False else re.split(r"\n(?=\(true|\(false)", out.strip()):
        ok = line.startswith("(true")
        v = [F(int(p) - int(n), 1 << int(ee)) for p, n, ee in re.findall(r"p := (\d+), n := (\d+) \}, e := (\d+)", line)]
        rows.append((ok, v, "none" in line))
    return rows, out


def consts_from(rows, a, b):
    """(s, C, L, B) from the leaves' readings, or None when some leaf does not decide."""
    kl, kh, pm, fa, fb = [], [], [], [], []
    for ok, v, has_none in rows:
        if not ok or has_none or len(v) != 8:
            return None
        k_lo, k_hi, p_lo, p_hi, fa_lo, fa_hi, fb_lo, fb_hi = v
        if not (k_lo > 0 and fa_hi <= 0 and fb_lo >= 0):
            return None
        kl.append(k_lo); kh.append(k_hi); pm.append(max(abs(p_lo), abs(p_hi), F(1)))
    k_lo, k_hi, p = min(kl), max(kh), max(pm)
    s = 0
    while F(1, 1 << s) > k_lo:
        s += 1
    C = max(0, math.ceil(math.log2(float(k_hi))) + 1)
    L = max(0, math.ceil(math.log2(float(p))) + 1)
    B = max(0, math.ceil(math.log2(float(b - a))) + 1)
    return s, C, B, L


def verdict_to_lean(qtext, law, q, search, name, max_tries=10, keep=False):
    import znumjudge as ZJ
    import zimplicit as ZI
    qs = ZJ.parse_quantities(qtext)[0]
    g = ZJ._parse_arith(law, qs)
    cert = ZI.search_certificate(g, q, qs, search)
    if cert is None:
        return {"status": "no verdict", "why": "zimplicit found no certificate"}
    res = ZI.check_implicit(g, q, qs, cert)
    if not res[0] or not cert.get("unique") or res[1] is None:
        return {"status": "no verdict", "why": f"zimplicit: {res}"}
    lo, hi = F(res[1][0]), F(res[1][1])
    slo0, shi0 = F(str(search[0])), F(str(search[1]))
    if lo <= slo0 or hi >= shi0:
        return {"status": "no verdict", "why": "the range touches the search end: a root is unique where it exists, "
                "but not every parameter vector has one in the search range", "range": (lo, hi)}
    try:
        xe, names, idx = Z.law_xe(g, q, qs)
    except ValueError as ex:
        return {"status": "not translated", "why": str(ex), "range": (lo, hi)}
    slo, shi = F(str(search[0])), F(str(search[1]))
    w = max(hi - lo, abs(lo) * F(1, 10 ** 6), F(1, 10 ** 12))
    a = Z.floor_dy(max(slo, lo - w / 2), 30)
    b = Z.ceil_dy(min(shi, hi + w / 2), 30)
    outer = {}
    for n in names:
        nlo, nhi = F(qs[n]["lo"]), F(qs[n]["hi"])
        outer[n] = (Z.floor_dy(nlo - F(1, 1 << Z.MU), Z.KD), Z.ceil_dy(nhi + F(1, 1 << Z.MU), Z.KD))
    ps = ps_of_box(names, idx, outer)
    # orientation from the float slope at the middle of the range
    mid = {n: float((outer[n][0] + outer[n][1]) / 2) for n in names}
    qm = float((lo + hi) / 2); h = max(abs(qm) * 1e-7, 1e-12)
    try:
        s0 = fl(g, {**mid, q: qm + h}) - fl(g, {**mid, q: qm - h})
    except (ValueError, ZeroDivisionError, OverflowError):
        s0 = 1.0
    neg = s0 < 0
    e = f"(.sub (.cst (⟨⟨0, 0⟩, 0⟩ : D)) {xe})" if neg else xe
    # proposals: one box, then covers on the parameters whose split helps the readings most (measured in Lean)
    def violation(row):
        ok, v, has_none = row
        if not ok or has_none or len(v) != 8:
            return float("inf")
        k_lo, _, _, _, _, fa_hi, fb_lo, _ = v
        return max(0.0, float(fa_hi)) + max(0.0, -float(fb_lo)) + max(0.0, -float(k_lo))
    cand = []
    if len(names) > 1:
        boxes_all, owner = [], []
        for n in names:
            for bx in leaf_boxes([(n, 4)], qs, outer):
                boxes_all.append(bx); owner.append(n)
        rows, _ = probe_leaves(e, names, idx, boxes_all, a, b, name + "_rank")
        score = {}
        for n, row in zip(owner, rows):
            score[n] = max(score.get(n, 0.0), violation(row))
        cand = sorted(names, key=lambda n: score.get(n, float("inf")))
    else:
        cand = list(names)
    proposals = [[]]
    for k in (2, 4, 8):
        if cand:
            proposals.append([(cand[0], k)])
    for k in (2, 3, 4, 6, 8):
        if len(cand) >= 2:
            proposals.append([(cand[0], k), (cand[1], k)])
    tried = []
    for splits in proposals[:max_tries]:
        boxes = leaf_boxes(splits, qs, outer)
        rows, out = probe_leaves(e, names, idx, boxes, a, b, name)
        cs = consts_from(rows, a, b)
        tried.append((splits, len(boxes), cs is not None))
        if cs is None:
            continue
        s_, C, B, L = cs
        if splits:
            tree = Z_tree(splits, idx, qs)
            body = (f"def lawT : PT := {tree}\n\ntheorem law_root (p : Nat → RExpr) (hin : InnerIn {Z.MU} p lawPS) :\n"
                    f"    ∃ x : RExpr, (rle (dv rOH qa) x ∧ rle x (dv rOH qb)) ∧ rEq (FP lawE qa lawPS p x) rzero ∧\n"
                    f"      ∀ y, rle (dv rOH qa) y → rle y (dv rOH qb) → rEq (FP lawE qa lawPS p y) rzero → rEq y x :=\n"
                    f"  tree_root lawE qa qb {s_} {C} {B} {L} {Z.MU} lawT lawPS (by decide +kernel) p hin\n")
        else:
            body = (f"theorem law_root (p : Nat → RExpr) (hin : InnerIn {Z.MU} p lawPS) :\n"
                    f"    ∃ x : RExpr, (rle (dv rOH qa) x ∧ rle x (dv rOH qb)) ∧ rEq (FP lawE qa lawPS p x) rzero ∧\n"
                    f"      ∀ y, rle (dv rOH qa) y → rle y (dv rOH qb) → rEq (FP lawE qa lawPS p y) rzero → rEq y x :=\n"
                    f"  par_root lawE qa qb lawPS {s_} {C} {B} {L} (by decide +kernel) p hin\n")
        text = (f"import ZRootPar\n/-! {name} — GENERATED by tools/zimplicit_lean.py from zimplicit's verdict on\n"
                f"    {law} = 0   ({q} in [{float(lo):.6g}, {float(hi):.6g}]{', negated' if neg else ''}) -/\n"
                f"namespace {name}\nopen ZNumBin ZIv ZXE ZRootExp ZRootDiv ZRootPVR ZRootPar VR.Numbers ZRealCF\n"
                f"def lawE : XE := {e}\ndef lawPS : PS := {ps}\ndef qa : D := {Z.dy(a)}\ndef qb : D := {Z.dy(b)}\n"
                + body + f"end {name}\n#print axioms {name}.law_root\n")
        out = run_lean(text, name)
        okk = f"'{name}.law_root' does not depend on any axioms" in out and "error" not in out
        if not keep:
            pass
        if okk:
            return {"status": "theorem", "range": (lo, hi), "bracket": (a, b), "negated": neg, "splits": splits,
                    "leaves": len(boxes), "consts": cs, "file": os.path.join(LEAN, "gen", name + ".lean"),
                    "tried": tried}
        tried[-1] = (splits, len(boxes), "kernel refused")
    return {"status": "refused", "range": (lo, hi), "bracket": (a, b), "tried": tried}


def Z_tree(splits, idx, qs):
    return Z.tree_text(splits, idx, qs)


if __name__ == "__main__":
    st = verdict_to_lean("pmax=[44.16,51.84] credit, Qmax=[0.038,0.042] credit, K=[27200,36800] credit, Q=? credit",
                         "pmax*(1 - Q/Qmax) - K*Q*Q", "Q", ["0", "0.06"], "ZBridgeFan")
    print(st)
