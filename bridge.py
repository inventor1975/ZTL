# -*- coding: utf-8 -*-
"""
The Python ↔ Lean stitch (seam #6): one questionnaire, two engines.

Generates a Lean file of #eval queries (truth tables of both registers,
J-operators, E and Δ, certified-engine verdicts on a shared battery —
propositional and quantified — and the stable lfp of the constant-free zoo; pure branch 2026-11-22:
the second register is the FORCED outcome t/f/n, its tables derived in Python from the readings),
runs it through `lake env lean` against the compiled corpus, and
compares every kernel-computed answer with the Python stands' answers.
Any divergence is a red light: the two implementations of ZTL must be
the same logic, mechanically.
"""

import subprocess
import sys
import os

from ztl import T, F, Z, VALUES, NOT, OPS2
from fixedpoint import least_fp_stable, N
from zread import _comb, _G, outcome
from zalgebra import jT, jF, jZ, dEq
from tableau import prove
from ztljudge import _forced

LEAN_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "lean")
GEN = os.path.join(LEAN_DIR, "BridgeGen.lean")

VNAMES = {T: "V.T", F: "V.F", Z: "V.Z"}


# ------------------------------------------------- shared formula specs
def to_lean_fm(phi):
    if phi == "p":
        return "(.atom 0)"
    if phi == "q":
        return "(.atom 1)"
    if phi == "T":
        return "(.top)"
    if phi == "F":
        return "(.bot)"
    op = phi[0]
    if op == "not":
        return f"(.neg {to_lean_fm(phi[1])})"
    name = {"and": "conj", "or": "disj", "imp": "imp",
            "xor": "xor", "xnor": "xnor"}[op]
    return f"(.{name} {to_lean_fm(phi[1])} {to_lean_fm(phi[2])})"


def allF_py(phi, rest):
    if not rest:
        return ("and", phi, phi)
    return ("and", phi, allF_py(rest[0], rest[1:]))


def exF_py(phi, rest):
    if not rest:
        return ("and", phi, phi)
    return ("or", phi, exF_py(rest[0], rest[1:]))


p, q = "p", "q"
ALLP = allF_py(p, [q])
EXP = exF_py(p, [q])

BATTERY = [
    ("MP", [p, ("imp", p, q)], q),
    ("LEM", [], ("or", p, ("not", p))),
    ("p->p", [], ("imp", p, p)),
    ("contraposition rule", [("imp", p, q)],
     ("imp", ("not", q), ("not", p))),
    ("dn-elimination", [("not", ("not", p))], p),
    ("non-contradiction", [], ("not", ("and", p, ("not", p)))),
    ("verum", [], "T"),
    ("ex falso", ["F"], p),
    ("falsum underivable", [], "F"),
    ("UI rule", [ALLP], p),
    ("EG law", [], ("imp", p, EXP)),
    ("drinker dom-2", [], exF_py(("imp", p, ALLP), [("imp", q, ALLP)])),
]

ZOO = [
    ("curry, bot = s and not s", {"s0": ("imp", "s0", "s1"), "s1": ("and", "s2", ("not", "s2")), "s2": "s2"},
     "[.imp (.atom 0) (.atom 1), .conj (.atom 2) (.neg (.atom 2)), .atom 2]"),
    ("strong liar", {"s0": ("and", ("not", "s0"), "s0")}, "[.conj (.neg (.atom 0)) (.atom 0)]"),
    ("liar", {"s0": ("not", "s0")}, "[.neg (.atom 0)]"),
    ("truth-teller", {"s0": "s0"}, "[.atom 0]"),
    ("carousel", {"s0": "s1", "s1": ("not", "s0")},
     "[.atom 1, .neg (.atom 0)]"),
    ("even cycle", {"s0": ("not", "s1"), "s1": ("not", "s0")},
     "[.neg (.atom 1), .neg (.atom 0)]"),
    ("russell", {"s0": "F", "s1": "F", "s2": ("not", "s0"),
                 "s3": "F", "s4": "T", "s5": ("not", "s4"),
                 "s6": "F", "s7": "F", "s8": ("not", "s8")},
     "[.bot, .bot, .neg (.atom 0), .bot, .top, .neg (.atom 4), "
     ".bot, .bot, .neg (.atom 8)]"),
    ("grounded chain", {"s0": "T", "s1": "s0",
                        "s2": ("or", ("not", "s1"), "s0")},
     "[.top, .atom 0, .disj (.neg (.atom 1)) (.atom 0)]"),
]

PH_NAMES = {T: "V.Ph.t", F: "V.Ph.f", N: "V.Ph.n"}


def _pair(x):
    return (x != F, x != T)


def ph_py(opn, x, y=None):
    """the forced outcome of a connective, derived from the READINGS (not from a table)"""
    if opn == "not":
        return {T: F, F: T, N: N}[x]
    return outcome(_comb(_G[opn], _pair(x), _pair(y)))
Z_LEAN = {"not": "V.znot", "and": "V.zand", "or": "V.zor",
          "imp": "V.zimp", "xor": "V.zxor", "xnor": "V.zxnor"}
PH_LEAN = {"not": "V.phNot", "and": "V.phAnd", "or": "V.phOr",
           "imp": "V.phImp", "xor": "V.phXor", "xnor": "V.phXnor"}


def _label_pool():
    """Formulas the receipt is asked about: every shape that can drop a
    branch's label, plus the ones where nothing may be dropped."""
    p_, q_ = "p", "q"
    base = [p_, q_, ("not", p_), ("not", ("not", p_))]
    out = list(base)
    for op in ("and", "or", "imp", "xor", "xnor"):
        out.append((op, p_, q_))
        out.append((op, ("not", p_), q_))
        out.append((op, p_, ("not", q_)))
        out.append((op, ("and", p_, q_), ("or", p_, q_)))
    out.append(("or", p_, ("not", p_)))
    out.append(("and", ("or", p_, ("not", p_)), ("or", q_, ("not", q_))))
    return out


def build_items():
    """(tag, lean #eval expression, expected answer as Lean text)."""
    items = []
    # both registers, every cell
    for opn in ("not", "and", "or", "imp", "xor", "xnor"):
        if opn == "not":
            for x in VALUES:
                items.append((f"greedy ¬{x}", f"{Z_LEAN[opn]} {VNAMES[x]}",
                              VNAMES[NOT(x)]))
            for x in (T, F, N):
                items.append((f"forced ¬{x}", f"{PH_LEAN[opn]} {PH_NAMES[x]}",
                              PH_NAMES[ph_py(opn, x)]))
        else:
            for x in VALUES:
                for y in VALUES:
                    items.append((f"greedy {opn}({x},{y})",
                                  f"{Z_LEAN[opn]} {VNAMES[x]} {VNAMES[y]}",
                                  VNAMES[OPS2[opn](x, y)]))
            for x in (T, F, N):
                for y in (T, F, N):
                    items.append((f"forced {opn}({x},{y})",
                                  f"{PH_LEAN[opn]} {PH_NAMES[x]} {PH_NAMES[y]}",
                                  PH_NAMES[ph_py(opn, x, y)]))
    # J-operators and the algebraic witnesses
    for x in VALUES:
        items.append((f"jT {x}", f"V.jT {VNAMES[x]}", VNAMES[jT(x)]))
        items.append((f"jF {x}", f"V.jF {VNAMES[x]}", VNAMES[jF(x)]))
        items.append((f"isZ {x}", f"V.isZ {VNAMES[x]}", VNAMES[jZ(x)]))
    for x in VALUES:
        for y in VALUES:
            e_py = OPS2["or"](NOT(OPS2["and"](x, x)), OPS2["and"](y, y))
            items.append((f"eimp({x},{y})",
                          f"V.eimp {VNAMES[x]} {VNAMES[y]}", VNAMES[e_py]))
            items.append((f"dEq({x},{y})",
                          f"V.dEq {VNAMES[x]} {VNAMES[y]}",
                          VNAMES[dEq(x, y)]))
    # the certified engine against the Python tableau
    for name, prems, concl in BATTERY:
        lean = ("V.tproves [" + ", ".join(to_lean_fm(x) for x in prems)
                + "] " + to_lean_fm(concl))
        items.append((f"tproves {name}", lean,
                      "true" if prove(prems, concl) else "false"))
    # THE RECEIPT. lean/Receipt.lean proves that whatever the label omits is
    # inert — but a theorem about `labF` only reaches the judge if `labF` IS
    # the judge's label. That is not an argument, it is a question for both
    # engines, so it is asked here like every other.
    for phi in _label_pool():
        for va in VALUES:
            for vb in VALUES:
                m = {"p": va, "q": vb}
                lab = _forced(phi, m)[1]
                lean_v = (f"(fun n => if n = 0 then {VNAMES[va]} "
                          f"else {VNAMES[vb]})")
                for atom, name in ((0, "p"), (1, "q")):
                    items.append(
                        (f"label {phi} {m} @{name}",
                         f"V.labF {lean_v} {to_lean_fm(phi)} {atom}",
                         "true" if name in lab else "false"))
    # stable lfp of the zoo (ZGround.lfp vs fixedpoint.least_fp_stable)
    for name, system, lean_sys in ZOO:
        lfp = least_fp_stable(system)
        expected = "[" + ", ".join(
            PH_NAMES[lfp[f"s{i}"]] for i in range(len(system))) + "]"
        items.append((f"lfp {name}", f"V.lfp {lean_sys}", expected))
    return items


def main():
    items = build_items()
    lines = ["import ZTL", "import TableauCert", "import ZAlgebra",
             "import ZGround", "import ZForced", "import Receipt", ""]
    for _, expr, _ in items:
        lines.append(f"#eval {expr}")
    with open(GEN, "w") as f:
        f.write("\n".join(lines) + "\n")

    r = subprocess.run(["lake", "build"], cwd=LEAN_DIR,
                       capture_output=True, text=True, timeout=600)
    if r.returncode != 0:
        print("lake build failed"); return 1
    r = subprocess.run(["lake", "env", "lean", GEN], cwd=LEAN_DIR,
                       capture_output=True, text=True, timeout=600)
    if r.returncode != 0:
        print("lean run failed:", r.stderr[:500]); return 1
    answers = [ln.strip() for ln in r.stdout.splitlines() if ln.strip()]
    if len(answers) != len(items):
        print(f"answer count mismatch: {len(answers)} vs {len(items)}")
        return 1
    bad = 0
    for (tag, _, expected), got in zip(items, answers):
        if got != expected:
            bad += 1
            print(f"  ✗ {tag}: Lean says {got}, Python says {expected}")
    print(f"  questions asked of both engines: {len(items)}")
    print(f"  divergences: {bad}")
    if bad == 0:
        print("  ✓ PYTHON ↔ LEAN: ALL ANSWERS COINCIDE — one logic, two engines")
        return 0
    print("  ✗ THE ENGINES DISAGREE — stop.")
    return 1


if __name__ == "__main__":
    print("=" * 72)
    print("THE STITCH: PYTHON STANDS AGAINST THE LEAN KERNEL")
    print("=" * 72)
    sys.exit(main())
