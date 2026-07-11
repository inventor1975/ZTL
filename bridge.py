# -*- coding: utf-8 -*-
"""
The Python ↔ Lean stitch (seam #6): one questionnaire, two engines.

Generates a Lean file of #eval queries (truth tables of both registers,
J-operators, E and Δ, certified-engine verdicts on a shared battery —
propositional and quantified — and lazy lfp of the constant-free zoo),
runs it through `lake env lean` against the compiled corpus, and
compares every kernel-computed answer with the Python stands' answers.
Any divergence is a red light: the two implementations of ZTL must be
the same logic, mechanically.
"""

import subprocess
import sys
import os

from ztl import T, F, Z, VALUES, NOT, OPS2
from fixedpoint import LAZY, least_fp_lazy
from zalgebra import jT, jF, jZ, dEq
from tableau import prove

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

K_PY = {"not": LAZY["not"], "and": LAZY["and"], "or": LAZY["or"],
        "imp": LAZY["imp"], "xor": LAZY["xor"], "xnor": LAZY["xnor"]}
Z_LEAN = {"not": "V.znot", "and": "V.zand", "or": "V.zor",
          "imp": "V.zimp", "xor": "V.zxor", "xnor": "V.zxnor"}
K_LEAN = {"not": "V.knot", "and": "V.kand", "or": "V.kor",
          "imp": "V.kimp", "xor": "V.kxor", "xnor": "V.kxnor"}


def build_items():
    """(tag, lean #eval expression, expected answer as Lean text)."""
    items = []
    # both registers, every cell
    for opn in ("not", "and", "or", "imp", "xor", "xnor"):
        if opn == "not":
            for x in VALUES:
                items.append((f"greedy ¬{x}", f"{Z_LEAN[opn]} {VNAMES[x]}",
                              VNAMES[NOT(x)]))
                items.append((f"lazy ¬{x}", f"{K_LEAN[opn]} {VNAMES[x]}",
                              VNAMES[K_PY[opn](x)]))
        else:
            for x in VALUES:
                for y in VALUES:
                    items.append((f"greedy {opn}({x},{y})",
                                  f"{Z_LEAN[opn]} {VNAMES[x]} {VNAMES[y]}",
                                  VNAMES[OPS2[opn](x, y)]))
                    items.append((f"lazy {opn}({x},{y})",
                                  f"{K_LEAN[opn]} {VNAMES[x]} {VNAMES[y]}",
                                  VNAMES[K_PY[opn](x, y)]))
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
    # lazy lfp of the constant-free zoo (ZGround.iter vs fixedpoint)
    for name, system, lean_sys in ZOO:
        lfp = least_fp_lazy(system)
        expected = "[" + ", ".join(
            VNAMES[lfp[f"s{i}"]] for i in range(len(system))) + "]"
        items.append((f"lfp {name}", f"V.lfp {lean_sys}", expected))
    return items


def main():
    items = build_items()
    lines = ["import ZTL", "import TableauCert", "import ZAlgebra",
             "import ZGround", ""]
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
