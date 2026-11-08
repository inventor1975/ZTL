"""zbound2lean — a requirement over a box of tolerances as a Lean THEOREM on VR's continuum (lean/ZBound.lean).

The curator, 2026-11-08: "важно, если стенд будет давать не только сертификат, но и доказательства". A requirement
`q op c` on a derived quantity q of a LINEAR system of laws (the stand's divider, a network's currents), for every
parameter vector in the box:

  1. q's expression from the laws — ZTL's own Cramer solution (zcertify.solve_system): `q = det_q / det` (said, not
     hidden: this elimination is Python's exact algebra, not proved in Lean; the theorem is about the expression);
  2. pinned quantities substituted; the box of the parameters rounded OUTWARD to dyadics (the theorem over the dyadic
     box covers the user's box — checked here in exact fractions);
  3. a bound `N/D <= p/r` CLEARED to `p·D − r·N >= 0` (`D > 0` on the box, checked by the kernel through `posOK`):
     a tight requirement (met exactly at a corner) stays provable — the corners of a polynomial read exactly;
  4. ZBound.findV (Lean, compiled `#eval`) PROPOSES a cover tree — monotone leaves, interval leaves, cuts — printed
     and pasted as a literal; the kernel checks only `chkV` (`decide +kernel`) and `bound_vrM` gives the theorem;
  5. a NEGATIVE CONTROL: the same tree against a bound tightened past the attained value must be refused.

Status: "theorem" (the kernel accepted), "no tree" (the search found none within its depth), "refused" (the kernel
did not accept), "not translated" (not a linear system, or a function ZXE lacks).
"""
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


def _subst(node, pinned):
    if isinstance(node, str):
        return pinned.get(node, node)
    if isinstance(node, (F, int)):
        return node
    op, *args = node
    if op == "sum":
        return ("sum", [_subst(a, pinned) for a in args[0]])
    return (op, *[_subst(a, pinned) for a in args])


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
    with open(path, "w") as f:
        f.write(text)
    r = subprocess.run(["lake", "env", "lean", path], cwd=LEAN, capture_output=True, text=True, timeout=3000)
    return r.stdout + r.stderr


def _box_lean(params, box):
    """`fun i => cond (Nat.beq i 0) (some (lo, hi)) (cond ... none)`."""
    body = "none"
    for i in reversed(range(len(params))):
        lo, hi = box[params[i]]
        body = f"(cond (Nat.beq i {i}) (some ({Z.dy(lo)}, {Z.dy(hi)})) {body})"
    return f"fun i => {body}"


def bound_to_lean(laws, unknowns, qtext, target, reqs, name, depth=14, trees=None):
    """laws: "lhs == rhs" strings; unknowns: the derived quantities; qtext: the sheet ("R1=[990,1010] credit, ...");
    target: the derived quantity; reqs: [(">=", c) | ("<=", c)]; name: the Lean namespace. `trees`: given trees
    (the search skipped) — the negative control pastes an accepted tree under a false bound."""
    import znumjudge as ZJ
    import zcertify as ZC
    qs = ZJ.parse_quantities(qtext)[0]
    try:
        sol = ZC.solve_system(laws, unknowns, qs)
    except Exception as ex:
        return {"status": "not translated", "why": f"not a linear square system: {ex}"}
    node = sol[target]
    pinned = {n: F(q["lo"]) for n, q in qs.items() if n not in unknowns and q["lo"] == q["hi"]
              and not isinstance(q["lo"], float)}
    node = _subst(node, pinned)
    params = sorted(n for n in _names(node, set()) if n in qs and n not in pinned)
    for n in params:
        if isinstance(qs[n]["lo"], float) or isinstance(qs[n]["hi"], float):
            return {"status": "not translated", "why": f"{n} is unbounded"}
    idx = {n: i for i, n in enumerate(params)}
    box = {n: (_dy_out(qs[n]["lo"], False), _dy_out(qs[n]["hi"], True)) for n in params}
    assert all(box[n][0] <= F(qs[n]["lo"]) and F(qs[n]["hi"]) <= box[n][1] for n in params)
    env = {n: float((box[n][0] + box[n][1]) / 2) for n in params}
    quotient = isinstance(node, tuple) and node[0] == "div"
    if quotient:
        Nn, Dn = node[1], node[2]
        if K.fl(Dn, env) < 0:                        # a negative determinant: both signs turned
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
        forms.append((op, c, form))
    gen = os.path.join(LEAN, "gen"); os.makedirs(gen, exist_ok=True)
    head = f"""import ZBound
open VR VR.Numbers ZNumBin ZField ZPoly ZIv ZXE ZRealCF ZRootDiv ZBound
namespace {name}
def B : Box := {_box_lean(params, box)}
def xQ : XE := {xe_q}
{"def xN : XE := " + xe_N if quotient else ""}
{"def xD : XE := " + xe_D if quotient else ""}
"""
    vs = "[" + ", ".join(str(i) for i in range(len(params))) + "]"
    probe = head + "".join(
        f'def F{k} : XE := {form}\n#eval IO.println (match findV true F{k} {Z.dy(0)} {vs} {depth} B with '
        f'| some t => "TREE" ++ toString {k} ++ " " ++ t.txt | none => "NOTREE" ++ toString {k})\n'
        for k, (_, _, form) in enumerate(forms)) + f"end {name}\n"
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
    for k, (op, c, form) in enumerate(forms):
        body += f"""def F{k} : XE := {form}
def T{k} : VT := {trees[k]}
theorem cleared{k} : ∀ x : Nat → RExpr, InBox rCF B x → rCF.le (dv rOH {Z.dy(0)}) (evR x F{k}) :=
  bound_vrM (lo := true) (vs := {vs}) (T := T{k}) (by decide +kernel) (by decide +kernel)
"""
    if quotient:
        body += f"""theorem q_pos (x : Nat → RExpr) (hx : InBox rCF B x) :
    rCF.pos (evR x xD) ∧ rCF.r (rCF.mul (evR x xD) (evR x xQ)) (evR x xN) :=
  div_value hx (a := xN) (b := xD) (by decide +kernel)
"""
    body += f"end {name}\n" + "".join(f"#print axioms {name}.cleared{k}\n" for k in range(len(forms)))
    if quotient:
        body += f"#print axioms {name}.q_pos\n"
    path = os.path.join(gen, name + ".lean")
    out = _run(body, path)
    ok = "error" not in out and out.count("does not depend on any axioms") == len(forms) + (1 if quotient else 0)
    res = {"status": "theorem" if ok else "refused", "file": path, "params": params, "box": box,
           "quotient": quotient, "trees": trees, "out": out[:600]}
    return res


def main():
    # the stand's divider (examples/divider-1pct-req-1pct.json, the design R1 = R2 = 1 kΩ, ±1 %)
    laws = ["Vin - Vout == I*R1", "Vout == I*R2"]
    qt = "Vin=5 credit, R1=[990,1010] credit, R2=[990,1010] credit, I=? credit, Vout=? credit"
    st = bound_to_lean(laws, ["I", "Vout"], qt, "Vout", [(">=", "2.475"), ("<=", "2.525")], "ZGenDivider")
    print({k: v for k, v in st.items() if k != "out"})


if __name__ == "__main__":
    main()
