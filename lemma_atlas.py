# -*- coding: utf-8 -*-
"""
lemma_atlas — run the *named* classical laws through the ZTL core and report,
for each, the real verdict: does it stand, and if it falls, exactly where.

Not counts (that is zrefuter's closed form) — concrete answers: modus ponens
holds; excluded middle FALLS at p=Z; contraction FALLS; here is the killing
Z-marking and how many verified inputs it takes to break it.

Everything here is MEASURED by ztl.ev over all {T,F,Z} assignments — nothing
is hand-computed (the core is the arbiter).
"""

import os
import sys
from itertools import product

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "tool"))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from ztl import T, F, Z, VALUES, ev          # noqa: E402
import zfl                                    # noqa: E402
from refuter import _atoms_core              # noqa: E402

# ---- the corpus of named laws (school + standard propositional logic) -------
# name -> ZFL formula string.  '<->' is written xnor (T iff both sides equal).
LAWS = [
    ("Identity  p→p",                    "imp(p,p)"),
    ("Excluded middle  p∨¬p",            "or(p,not(p))"),
    ("Non-contradiction  ¬(p∧¬p)",       "not(and(p,not(p)))"),
    ("Double-negation elim  ¬¬p→p",      "imp(not(not(p)),p)"),
    ("Double-negation intro  p→¬¬p",     "imp(p,not(not(p)))"),
    ("Modus ponens  (p→q)∧p ⊢ q",        "imp(and(imp(p,q),p),q)"),
    ("Modus tollens  (p→q)∧¬q ⊢ ¬p",     "imp(and(imp(p,q),not(q)),not(p))"),
    ("Hypothetical syllogism",           "imp(and(imp(p,q),imp(q,r)),imp(p,r))"),
    ("Disjunctive syllogism",            "imp(and(or(p,q),not(p)),q)"),
    ("Contraposition  (p→q)→(¬q→¬p)",    "imp(imp(p,q),imp(not(q),not(p)))"),
    ("Contraction  (p→(p→q))→(p→q)",     "imp(imp(p,imp(p,q)),imp(p,q))"),
    ("Weakening  p→(q→p)",               "imp(p,imp(q,p))"),
    ("Peirce  ((p→q)→p)→p",              "imp(imp(imp(p,q),p),p)"),
    ("Ex falso  (p∧¬p)→q",               "imp(and(p,not(p)),q)"),
    ("Simplification  p∧q→p",            "imp(and(p,q),p)"),
    ("Addition  p→p∨q",                  "imp(p,or(p,q))"),
    ("De Morgan 1  ¬(p∧q)↔¬p∨¬q",        "xnor(not(and(p,q)),or(not(p),not(q)))"),
    ("De Morgan 2  ¬(p∨q)↔¬p∧¬q",        "xnor(not(or(p,q)),and(not(p),not(q)))"),
    ("Distributivity ∧/∨",               "xnor(and(p,or(q,r)),or(and(p,q),and(p,r)))"),
    ("Commutativity ∧",                  "xnor(and(p,q),and(q,p))"),
    ("Idempotence ∧  p∧p↔p",             "xnor(and(p,p),p)"),
    ("Absorption  p∧(p∨q)↔p",            "xnor(and(p,or(p,q)),p)"),
    ("Import-export",                    "xnor(imp(and(p,q),r),imp(p,imp(q,r)))"),
    ("Material impl  (p→q)↔(¬p∨q)",      "xnor(imp(p,q),or(not(p),q))"),
    ("Reductio  (¬p→p)→p",               "imp(imp(not(p),p),p)"),
]


def classify(formula_str):
    """MEASURED verdict for one law over {T,F,Z}. Returns dict."""
    tree = zfl.parse_formula(formula_str)
    core = zfl.to_core_formula(tree)
    atoms = _atoms_core(core)
    holds_classical = True
    class_ce = None
    z_kills = []                 # killing assignments that use a Z
    for combo in product(VALUES, repeat=len(atoms)):
        env = dict(zip(atoms, combo))
        if ev(core, env) != T:
            if any(v == Z for v in combo):
                z_kills.append(env)
            else:
                holds_classical = False
                if class_ce is None:
                    class_ce = env
    if not holds_classical:
        return {"verdict": "INVALID (classical error)", "atoms": atoms,
                "witness": class_ce, "depth": None, "allZ_survives": None}
    if not z_kills:
        return {"verdict": "VALID (robust under Z)", "atoms": atoms,
                "witness": None, "depth": None, "allZ_survives": True}
    # fragile: report the shallowest break + whether it survives full ignorance
    depth = min(sum(1 for v in e.values() if v != Z) for e in z_kills)
    allZ = ev(core, {a: Z for a in atoms}) == T
    # a shallowest witness
    shallow = min(z_kills, key=lambda e: sum(1 for v in e.values() if v != Z))
    return {"verdict": "FRAGILE (falls under Z)", "atoms": atoms,
            "witness": shallow, "depth": depth, "allZ_survives": allZ}


def _fmt_env(env):
    return ", ".join(f"{a}={v}" for a, v in env.items()) if env else "—"


def main():
    rows = []
    for name, f in LAWS:
        r = classify(f)
        rows.append((name, f, r))
    # console
    for name, f, r in rows:
        print(f"{name}")
        print(f"    {f}")
        print(f"    → {r['verdict']}")
        if r["witness"] is not None:
            tag = ("survives full ignorance, " if r["allZ_survives"]
                   else "fails-open, ") if r["depth"] is not None else ""
            print(f"      falls at:  {_fmt_env(r['witness'])}"
                  + (f"   [{tag}min {r['depth']} verified to break]"
                     if r["depth"] is not None else ""))
        print()
    return rows


if __name__ == "__main__":
    main()
