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

RU_KIND = {
    "PARADOX": "ПАРАДОКС — классических решений нет; отказ ВЕЧНЫЙ",
    "UNDERDETERMINED": "НЕДООПРЕДЕЛЁННОСТЬ — отказ до внешнего выбора",
    "INPUT": "непроверенный вход — отказ до верификации",
    "DOWNSTREAM": "заражение сверху (см. виновных)",
    "GROUNDED": "заземлено",
}


def run_statement(doc, parsed):
    env, formula = to_statement(doc, parsed)
    value = ev(formula, env)
    marking = {a: (v if v in (T, F) else "M") for a, v in env.items()}
    stable = stable_bit(formula, marking)
    z_atoms = sorted(a for a, v in env.items() if v == Z)

    if value == T:
        cls = ("стабильное T — можно строить дом" if stable
               else "T до-верификации — лестничный рапорт, живёт до первой проверки")
    else:
        cls = ("стабильное F — заработанное опровержение" if stable
               else "F до-верификации — default deny, отказ до проверки входов")

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
        "warranty": "стабильный" if stable else "до-верификации",
        "verdict_class": cls,
        "z_atoms": z_atoms,
        "passport": ("все атомы поверены — вердикт классический"
                     if not z_atoms else
                     f"непроверенные входы: {', '.join(z_atoms)}"
                     " — отказные части снимаются верификацией"),
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
            "kind_ru": RU_KIND.get(kind, kind), "detail": detail})
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
        "summary": (f"заземлено {len(grounded)} из {len(lfp)};"
                    f" в карантине: {', '.join(quarantined) or 'никого'}"),
    }


def run(doc, parsed):
    if doc["genre"] == "statement":
        return run_statement(doc, parsed)
    return run_system(doc, parsed)
