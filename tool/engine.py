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

from ztl import T, F, Z, VALUES, ev, atoms, show         # noqa: E402
from zverify import grade, ztl_eval, verify              # noqa: E402
from zpassport import passports, deps, component_models  # noqa: E402
from zfl import to_statement, to_system                  # noqa: E402
import zderive                                           # noqa: E402
from entailment import entails                           # noqa: E402

KIND_TXT = {
    "PARADOX": "PARADOX — no classical solutions; refusal PERMANENT",
    "INTRINSIC": "INTRINSIC — ungrounded, yet uniquely consistent:"
                 " the stipulation is forced",
    "UNDERDETERMINED": "UNDERDETERMINED — refusal until an external choice",
    "INPUT": "unverified input — refusal until verification",
    "DOWNSTREAM": "inherited from above (see the culprits)",
    "GROUNDED": "grounded",
}


def run_statement(doc, parsed):
    env, formula = to_statement(doc, parsed)
    value = ev(formula, env)
    marking = {a: (v if v in (T, F) else "M") for a, v in env.items()}
    g = grade(formula, marking)
    z_atoms = sorted(a for a, v in env.items() if v == Z)

    if value == T:
        cls = {"hereditary": "hereditary T — build on it: no verification"
                             " path can revoke it",
               "sound": "sound T — never a lie (every completion agrees),"
                        " but the verdict may stall to refusal before"
                        " verification completes",
               "until-verification": "T until verification — a ladder report,"
                                     " alive till the first check"}[g]
    else:
        cls = {"hereditary": "hereditary F — no verification path can"
                             " revoke the refusal",
               "sound": "sound F — an earned-in-all-completions refutation,"
                        " though the verdict may shift mid-verification",
               "until-verification": "F until verification — default deny,"
                                     " refusal until the inputs are checked"}[g]

    completions = []
    if 0 < len(z_atoms) <= 3:
        for combo in product((T, F), repeat=len(z_atoms)):
            env2 = dict(env)
            env2.update(dict(zip(z_atoms, combo)))
            completions.append({
                "case": ", ".join(f"{a}={v}" for a, v in zip(z_atoms, combo)),
                "value": ev(formula, env2)})

    report = {
        "genre": "statement",
        "verdict": value,
        "warranty": g,
        "verdict_class": cls,
        "z_atoms": z_atoms,
        "passport": ("all atoms verified — the verdict is classical"
                     if not z_atoms else
                     f"unverified inputs: {', '.join(z_atoms)}"
                     " — the refusals are liftable by verification"),
        "completions": completions,
    }
    # A constant completion table means the verdict reads none of the
    # unverified atoms: the assertion is a FRAME, not a fact — a test
    # that cannot fail is not a test (the Girard cell).
    if len(completions) > 1 and len({c["value"] for c in completions}) == 1:
        report["frame"] = ("constant over all completions — a frame, not a"
                           " fact: the assertion reads none of its"
                           " unverified atoms; a test that cannot fail is"
                           " not a test")

    # --- the temporal extension (E24): play the verification timeline.
    # Logical time: one tick = one act verify(mark -> earned value); the
    # verdict is a pair (value, warranty grade) and the chronicle shows
    # how the grade travels the ladder: until-verification = true NOW,
    # sound = true at every ending, hereditary = true always (on the
    # shelf). Once hereditary, the remaining checks buy nothing.
    tl = doc.get("timeline")
    if tl:
        m = dict(marking)
        prev_g, settled_at = g, None
        chronicle = [{"tick": 0, "event": "start", "verdict": value,
                      "warranty": g,
                      "marks_left": sum(1 for s in m.values() if s == "M")}]
        for i, ev_ in enumerate(tl, start=1):
            a, val = ev_["atom"], ev_["value"]
            prev_v = ztl_eval(formula, m)
            m = verify(m, a, val)
            v2, g2 = ztl_eval(formula, m), grade(formula, m)
            left = sum(1 for s in m.values() if s == "M")
            step = {"tick": i, "event": f"{a} := {val}", "verdict": v2,
                    "warranty": g2, "marks_left": left}
            notes = []
            if v2 != prev_v:
                notes.append("the verdict FLIPS")
            if prev_g == "until-verification" and g2 == "hereditary":
                notes.append("U->H: the ground arrived all at once")
            if prev_g == "sound" and g2 == "until-verification":
                notes.append("S->U: the credit worsened before settling")
            if g2 == "hereditary" and settled_at is None:
                settled_at = i
                saved_at_settle = left
                if left > 0:
                    notes.append(f"SETTLED EARLY — {left} check(s) still"
                                 " unverified buy NOTHING now")
            if notes:
                step["note"] = "; ".join(notes)
            chronicle.append(step)
            prev_g = g2
        report["chronicle"] = chronicle
        report["settled_at"] = settled_at
        report["checks_saved"] = (saved_at_settle
                                  if settled_at is not None else 0)
    return report


def _split_and(f):
    """Flatten a top-level conjunction into a premise list."""
    if isinstance(f, tuple) and f[0] == "and":
        return _split_and(f[1]) + _split_and(f[2])
    return [f]


def logic_map(doc, parsed):
    """The Assertion tab: the assertion's LOGIC MAP on top of the
    statement report — (a) its currency (free ZTL truth / classically
    valid but ON CREDIT / contingent), (b) the decisive verifications,
    (c) for an implication-shaped assertion, the E26 derivation audit:
    earned / on credit (which loan) / rules-gap / does not follow."""
    report = run_statement(doc, parsed)
    env, formula = to_statement(doc, parsed)
    names = sorted(atoms(formula))
    marking = {a: (v if v in (T, F) else "M") for a, v in env.items()}

    # ---- (a) currency: what the assertion's truth is made of ----------
    from itertools import product as _prod
    classical_valid = all(
        ev(formula, dict(zip(names, c))) == T
        for c in _prod((T, F), repeat=len(names))) if names else \
        ev(formula, {}) == T
    ztl_tautology = all(
        ev(formula, dict(zip(names, c))) == T
        for c in _prod(VALUES, repeat=len(names))) if names else \
        ev(formula, {}) == T
    if ztl_tautology:
        currency = {"kind": "free-truth",
                    "note": "a guarded ZTL tautology — true under every "
                            "assignment INCLUDING unverified inputs; "
                            "this truth costs nothing"}
    elif classical_valid:
        witness = next(
            dict(zip(names, c)) for c in _prod(VALUES, repeat=len(names))
            if ev(formula, dict(zip(names, c))) != T)
        currency = {"kind": "on-credit",
                    "witness": {a: v for a, v in witness.items()},
                    "note": "classically valid — yet it BREAKS when an "
                            "input is unverified: truth minted from form, "
                            "not from ground; the killing marking is the "
                            "witness"}
    else:
        cm = next((dict(zip(names, c))
                   for c in _prod((T, F), repeat=len(names))
                   if ev(formula, dict(zip(names, c))) != T), None)
        currency = {"kind": "contingent",
                    "witness": cm or {},
                    "note": "not a law — its truth depends on the facts; "
                            "the witness is a classical countermodel"}

    # ---- (b) decisive verifications (which single checks flip it) -----
    decisive = []
    cur = ztl_eval(formula, marking)
    for a in names:
        if marking.get(a) != "M":
            continue
        flips = {v: ztl_eval(formula, verify(marking, a, v))
                 for v in (T, F)}
        if any(v != cur for v in flips.values()):
            decisive.append({"atom": a, "T": flips[T], "F": flips[F]})

    # ---- (c) the derivation audit (E26) for implication shapes --------
    audit = None
    if isinstance(formula, tuple) and formula[0] == "imp":
        premises = _split_and(formula[1])
        target = formula[2]
        if len(names) > 3:
            audit = {"status": "skipped",
                     "note": "audit pool is bounded to 3 atoms"}
        else:
            pool = zderive.build_pool(names)
            ps = set(pool)
            if any(p not in ps for p in premises) or target not in ps:
                audit = {"status": "skipped",
                         "note": "a premise or the conclusion is deeper "
                                 "than the bounded audit pool"}
            else:
                D = zderive.close(premises, pool=pool)
                if target in D:
                    audit = {"status": "earned",
                             "chain": zderive.chain(D, target),
                             "note": "reachable by the 12 alive rules "
                                     "alone — every step transports "
                                     "earned truth, no borrowing"}
                else:
                    unlocked = None
                    for loans in ({"DNE"}, {"TAUT"}, {"DNE", "TAUT"}):
                        D2 = zderive.close(premises, loans=loans, pool=pool)
                        if target in D2:
                            unlocked = (loans, D2)
                            break
                    if unlocked:
                        loans, D2 = unlocked
                        audit = {"status": "on-credit",
                                 "loans": sorted(loans),
                                 "chain": zderive.chain(D2, target),
                                 "note": "every chain to the conclusion "
                                         "must borrow a FALLEN rule — the "
                                         "inference stands only on credit"}
                    elif entails(premises, target) is None:
                        audit = {"status": "rules-gap",
                                 "note": "semantically forced (every "
                                         "assignment making the premises "
                                         "T makes the conclusion T), yet "
                                         "no chain in the measured rule "
                                         "battery reaches it on this pool"}
                    else:
                        ce = entails(premises, target)
                        audit = {"status": "does-not-follow",
                                 "counterexample": ce,
                                 "note": "the conclusion is not entailed "
                                         "by the premises — the "
                                         "counterexample assignment makes "
                                         "the premises T and the "
                                         "conclusion non-T"}

    report["logic_map"] = {"formula": show(formula),
                           "currency": currency,
                           "decisive": decisive,
                           "audit": audit}
    return report


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
        if kind in ("UNDERDETERMINED", "INTRINSIC"):
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
