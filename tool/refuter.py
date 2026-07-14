# -*- coding: utf-8 -*-
"""
ZTL hypothesis refuter (Opus, 2026-07-14).

The studio's "Hypotheses" mode. A hypothesis is a claimed law/rule — a ZFL
*statement*. The core checks it EXHAUSTIVELY over all {T,F,Z} assignments
(decidable → the answer is guaranteed). The twist a classical checker
cannot ask: does the rule still hold when some inputs are UNVERIFIED (Z)?

Outcomes:
  * CONFIRMED             — holds under every assignment, incl. unverified.
  * REFUTED_CLASSICAL     — fails already on {T,F}: a plain logic error.
  * REFUTED_UNCERTAINTY   — holds classically, but BREAKS when an input is
                            unverified. The killing marking is shown.

Public entry points:
  refute_zfl(zfl_text) — for the studio (takes a ZFL statement document).
  refute(formula_str)  — for the CLI (takes a bare ZFL formula string).
"""

import os
import sys
from itertools import product

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))                       # tool/
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))      # repo root

from ztl import T, F, Z, VALUES, ev                       # noqa: E402
import zfl                                                # noqa: E402


def _atoms_core(formula, acc=None):
    """Collect atom names of a ztl.py core formula (str = atom, tuple = op)."""
    if acc is None:
        acc = []
    if isinstance(formula, str):
        if formula not in ("T", "F") and formula not in acc:
            acc.append(formula)
    elif isinstance(formula, tuple):
        for x in formula[1:]:
            _atoms_core(x, acc)
    return acc


def _check(formula, atoms):
    """Exhaustive {T,F,Z} check of a core formula. Returns the report dict."""
    if not atoms:
        v = ev(formula, {})
        return {"atoms": [], "outcome": "CONFIRMED" if v == T else
                "REFUTED_CLASSICAL", "counterexample": None}

    classical_ce = None
    uncertain_ce = None
    holds_classically = True
    for combo in product(VALUES, repeat=len(atoms)):
        env = dict(zip(atoms, combo))
        if ev(formula, env) != T:
            if any(v == Z for v in combo):
                if uncertain_ce is None:
                    uncertain_ce = env
            else:
                holds_classically = False
                if classical_ce is None:
                    classical_ce = env

    if uncertain_ce is None and classical_ce is None:
        return {"atoms": atoms, "outcome": "CONFIRMED", "counterexample": None}
    if not holds_classically:
        return {"atoms": atoms, "outcome": "REFUTED_CLASSICAL",
                "counterexample": classical_ce}
    return {"atoms": atoms, "outcome": "REFUTED_UNCERTAINTY",
            "counterexample": uncertain_ce}


def refute_zfl(zfl_text):
    """Studio entry: a hypothesis is a ZFL 'statement' (a claimed law)."""
    doc, parsed, issues = zfl.validate(zfl_text)
    if parsed is None:
        return {"ok": False, "issues": issues}
    if doc.get("genre") != "statement":
        return {"ok": False, "issues": [{
            "level": "error", "code": "E_GENRE", "where": "genre",
            "hint": "a hypothesis is a claimed law — use genre \"statement\" "
                    "with an \"assert\" formula, not a self-referential "
                    "\"system\"."}]}
    env, formula = zfl.to_statement(doc, parsed)
    atoms = _atoms_core(formula)
    rep = _check(formula, atoms)
    rep["ok"] = True
    return rep


def refute(formula_str):
    """CLI entry: a bare ZFL formula string, e.g. 'imp(p,p)'."""
    tree = zfl.parse_formula(formula_str)
    formula = zfl.to_core_formula(tree)
    rep = _check(formula, _atoms_core(formula))
    rep["formula"] = formula_str
    return rep


def report(formula_str):
    """Human-readable one-block CLI report."""
    r = refute(formula_str)
    o = r["outcome"]
    lines = [f"HYPOTHESIS : {formula_str}",
             f"atoms      : {', '.join(r['atoms']) or '(none)'}"]
    if o == "CONFIRMED":
        lines.append("VERDICT    : CONFIRMED — holds under EVERY assignment,")
        lines.append("             including any unverified (Z) inputs.")
    elif o == "REFUTED_CLASSICAL":
        ce = ", ".join(f"{a}={v}" for a, v in r["counterexample"].items())
        lines.append("VERDICT    : REFUTED (classically) — fails on verified")
        lines.append(f"             inputs.  counterexample: {ce}")
    else:
        ce = r["counterexample"]
        cs = ", ".join(f"{a}={v}" for a, v in ce.items())
        zs = ", ".join(a for a, v in ce.items() if v == Z)
        lines.append("VERDICT    : REFUTED (under uncertainty) — holds when")
        lines.append("             verified, breaks when an input is unverified.")
        lines.append(f"             killing marking: {cs}  (unverified: {zs})")
    return "\n".join(lines)


DEMO = ["imp(p,p)", "imp(not(p),not(p))", "or(p,not(p))",
        "imp(and(a,b),a)", "imp(a,or(a,b))"]

if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] != "--demo":
        print(report(" ".join(sys.argv[1:])))
    else:
        for f in DEMO:
            print(report(f)); print()
