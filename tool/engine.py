# -*- coding: utf-8 -*-
"""
ZTLStudio: the arbiter. Runs validated ZFL on the ZTL core and renders
a structured report. Deliberately AI-free: the verdicts come from the
measured engines (ztl / zverify / zpassport), nothing else.
"""

import os
import sys
from itertools import product

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ztl import T, F, Z, VALUES, ev                      # noqa: E402
from zverify import stable_bit, ztl_eval                 # noqa: E402
from zpassport import passports, deps, component_models  # noqa: E402
from zfl import to_statement, to_system                  # noqa: E402

KIND_TXT = {
    "PARADOX": "PARADOX — no classical solutions; refusal PERMANENT",
    "UNDERDETERMINED": "UNDERDETERMINED — refusal until an external choice",
    "INPUT": "unverified input — refusal until verification",
    "DOWNSTREAM": "inherited from above (see the culprits)",
    "GROUNDED": "grounded",
}


def run_statement(doc, parsed):
    env, formula = to_statement(doc, parsed)
    value = ev(formula, env)
    marking = {a: (v if v in (T, F) else "M") for a, v in env.items()}
    stable = stable_bit(formula, marking)
    z_atoms = sorted(a for a, v in env.items() if v == Z)

    if value == T:
        cls = ("stable T — build on it" if stable
               else "T until verification — a ladder report,"
                    " alive till the first check")
    else:
        cls = ("stable F — an earned refutation" if stable
               else "F until verification — default deny,"
                    " refusal until the inputs are checked")

    completions = []
    if 0 < len(z_atoms) <= 3:
        for combo in product((T, F), repeat=len(z_atoms)):
            env2 = dict(env)
            env2.update(dict(zip(z_atoms, combo)))
            completions.append({
                "case": ", ".join(f"{a}={v}" for a, v in zip(z_atoms, combo)),
                "value": ev(formula, env2)})

    return {
        "genre": "statement",
        "verdict": value,
        "warranty": "stable" if stable else "until-verification",
        "verdict_class": cls,
        "z_atoms": z_atoms,
        "passport": ("all atoms verified — the verdict is classical"
                     if not z_atoms else
                     f"unverified inputs: {', '.join(z_atoms)}"
                     " — the refusals are liftable by verification"),
        "completions": completions,
    }


def run_system(doc, parsed):
    system = to_system(doc, parsed)
    lfp, reports, kinds = passports(system)

    grounded = {s: v for s, v in sorted(lfp.items()) if v in (T, F)}
    quarantined = sorted(s for s, v in lfp.items() if v == Z)

    passport_rows = []
    stipulations = []
    for comp, kind, detail in reports:
        passport_rows.append({
            "component": comp, "kind": kind,
            "kind_txt": KIND_TXT.get(kind, kind), "detail": detail})
        if kind == "UNDERDETERMINED":
            names = set(comp)
            env_names = set()
            for s in comp:
                env_names |= deps(system[s]) - names
            env = {n: lfp[n] for n in env_names}
            models = component_models(comp, system, env)
            stipulations.append({
                "component": comp,
                "models": [", ".join(f"{k}={v}" for k, v in sorted(m.items()))
                           for m in models]})

    return {
        "genre": "system",
        "grounded": grounded,
        "quarantined": quarantined,
        "passports": passport_rows,
        "stipulations": stipulations,
        "summary": (f"grounded {len(grounded)} of {len(lfp)};"
                    f" quarantined: {', '.join(quarantined) or 'none'}"),
    }


def run(doc, parsed):
    if doc["genre"] == "statement":
        return run_statement(doc, parsed)
    return run_system(doc, parsed)
