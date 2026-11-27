# -*- coding: utf-8 -*-
"""
zplan — THE CHEAPEST PLAN OF CHECKS THAT SETTLES A CLAIM WHATEVER THE CHECKS SHOW.

(2026-11-27, the curator: "Строй в ЗТЛ правь ядро"; "для судьи нужно делать оптимально, так как мы только теоремы там
принимаем. Если нет оптимального то скажи". Written with AI.)

WHAT THE KERNEL ALREADY HAS. The backward pass (zbackward.py, zbackward_tree.py, lean/ZBackward.lean) names minimal
SETS of dirty grounds: POSSIBILITY (some filling of the set reaches the target) and GUARANTEE (every filling does).
It counts grounds; it does not know what a check costs, and a set is checked whole.

WHAT IS ADDED HERE. Every dirty ground has a COST of checking it, and the checks are made ONE AFTER ANOTHER: what is
checked next may depend on what the last check showed. A plan is a tree — "check a; if it holds check b, if it fails
check c" — and it SETTLES the claim when every branch ends EARNED or REFUTED (the judge's own dispositions). Its
price is its dearest branch: what must be paid in the worst case. The plan returned has the least such price over ALL
plans. For (a & b) | (~a & c) the least guaranteeing set is {a, b, c}; the plan "a, then b or c" never checks three.

THE THEOREM (lean/ZPlan.lean, zero axioms, for the kernel's own `earnedR` / `refutedR`): the recursion computed here —
nothing if settled, else over every dirty ground its cost plus the worse of the two continuations, the least of these —
is a lower bound for every valid plan (`opt_le`), is attained by a valid plan (`opt_attained`), hence is the optimum
(`optimal`). inventory/zplan_lean_bridge.py has the Lean kernel compute the same numbers.

THREE DIFFERENT QUESTIONS, never mixed (as zbackward keeps POSSIBILITY and GUARANTEE apart):
    worst_case     the cheapest plan that settles it WHATEVER the checks show            <- the order to act on
    cheapest_set   the cheapest set to check together that settles it whatever they show (never cheaper than the plan)
    best_case      the cheapest checks after which it COULD be EARNED / REFUTED, if they come out that way
"Cheapest on average" is NOT here and cannot be without a premise: it needs the chances of the answers and how the
checks hang together, and how grounds hang together is the dirty parameter. No heuristic is offered in its place.

LIMITS, said aloud. The search is exponential in the number of dirty grounds (3^n markings, each judged once): up to
PLAN_CAP it is exact, beyond it the answer is a refusal, never an approximation. Costs are numbers in one unit — the
caller's unit; a ground with no cost stated is a refusal too. `hold`: grounds no check can settle (zfl's chance rows)
are never asked; if the claim cannot be settled without them, that is said ("no_plan").

    python3 test_zplan.py
"""
import itertools
import os
import sys
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from ztl import T, F, Z                                   # noqa: E402
from ztljudge import judge, _show, _atoms, formalize      # noqa: E402

PLAN_CAP = 10          # dirty grounds: 3^10 = 59049 markings, each judged once
TERMINAL = ("EARNED", "REFUTED")
MUTANT = {}            # TEST-ONLY sabotage switches; empty = the real plan


def _num(x):
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def _setup(claim, marking, costs, hold, cap):
    phi = formalize(claim) if isinstance(claim, str) else claim
    atoms = sorted(_atoms(phi))
    m = {a: marking.get(a, Z) for a in atoms}
    dirty = [a for a in atoms if m[a] == Z]
    ask = [a for a in dirty if a not in set(hold)]
    c = {}
    missing = [a for a in ask if a not in (costs or {}) or str(costs[a]).strip() == ""]
    if missing:
        return phi, m, dirty, ask, None, {"refused": f"no cost stated for {missing}: a plan by cost needs the cost of "
                                                     f"every ground it may check", "no_cost": missing}
    for a in ask:
        try:
            c[a] = Fr(str(costs[a]))
        except Exception:
            raise ValueError(f"the cost of {a!r}: {costs[a]!r} is not a number")
        if c[a] < 0:
            raise ValueError(f"the cost of {a!r}: {costs[a]!r} is negative")
    if len(ask) > cap:
        return phi, m, dirty, ask, c, {"refused": f"{len(ask)} dirty grounds; the plan is computed exactly up to {cap} "
                                                  f"(3^n markings, each judged) and is not approximated beyond"}
    return phi, m, dirty, ask, c, None


def plan(claim, marking, costs, hold=(), cap=PLAN_CAP):
    """-> {"already", "dirty", "held", "worst_case": {"cost", "plan", "checks_at_most"}, "cheapest_set", "best_case"}
    or {"refused": why}. See the module doc. claim: text or the kernel's AST; marking: {ground: T/F/Z};
    costs: {ground: number}."""
    phi, m, dirty, ask, c, no = _setup(claim, marking, costs, hold, cap)
    if no:
        return no
    text = _show(phi)
    disp = {}
    def settled(state):
        if state not in disp:
            mm = dict(m); mm.update(zip(ask, state))
            d = judge(text, mm)["disposition"]
            disp[state] = d if d in TERMINAL else None
        return disp[state]
    start = tuple(Z for _ in ask)
    out = {"already": bool(settled(start)), "dirty": dirty, "held": [a for a in dirty if a not in ask]}
    if out["already"]:
        out["verdict"] = settled(start)
        return out
    put = lambda state, i, x: state[:i] + (x,) + state[i + 1:]
    # THE RECURSION of lean/ZPlan.lean (`opt`): settled -> 0; else the least, over the dirty grounds, of the cost of
    # checking one plus the WORSE of the two continuations. None: no plan settles it from here (held grounds).
    memo = {}
    def best(state):
        if state in memo:
            return memo[state]
        d = settled(state)
        if d:
            memo[state] = (Fr(0), 0, {"verdict": d})
            return memo[state]
        found = None
        for i, a in enumerate(ask):
            if state[i] != Z:
                continue
            yes, no_ = best(put(state, i, T)), best(put(state, i, F))
            if yes is None or no_ is None:
                continue
            worse = min(yes[0], no_[0]) if MUTANT.get("best_branch") else max(yes[0], no_[0])
            key = (c[a] + worse, c[a], a)
            if found is None or key < found[0]:
                found = (key, 1 + max(yes[1], no_[1]),
                         {"check": a, "cost": _num(c[a]), "if_true": yes[2], "if_false": no_[2]})
        memo[state] = None if found is None else (found[0][0], found[1], found[2])
        return memo[state]
    w = best(start)
    if w is None:
        out["no_plan"] = ("no plan of checks settles it whatever they show: it rests on grounds no check can settle ("
                          + ", ".join(out["held"]) + ")") if out["held"] else "no plan of checks settles it"
    else:
        out["worst_case"] = {"cost": _num(w[0]), "checks_at_most": w[1], "plan": w[2]}
    # the cheapest SET checked together that settles it whatever it shows (zbackward's GUARANTEE, by cost)
    cheapest = None
    for k in range(1, len(ask) + 1):
        for idx in itertools.combinations(range(len(ask)), k):
            cost = sum((c[ask[i]] for i in idx), Fr(0))
            if cheapest is not None and (cost, k) >= (cheapest[0], len(cheapest[1])):
                continue
            ok = True
            for vals in itertools.product((T, F), repeat=k):
                s = list(start)
                for i, x in zip(idx, vals):
                    s[i] = x
                if not settled(tuple(s)):
                    ok = False
                    break
            if ok:
                cheapest = (cost, [ask[i] for i in idx])
    out["cheapest_set"] = None if cheapest is None else {"cost": _num(cheapest[0]), "check_together": cheapest[1]}
    # the cheapest checks after which it COULD be EARNED / REFUTED (zbackward's POSSIBILITY, by cost)
    bc = {}
    def could(state, target):
        key = (state, target)
        if key in bc:
            return bc[key]
        if settled(state) == target:
            bc[key] = (Fr(0), [])
            return bc[key]
        bc[key] = None                                     # (a marking is never revisited: grounds only get cleaner)
        found = None
        for i, a in enumerate(ask):
            if state[i] != Z:
                continue
            for x in (T, F):
                r = could(put(state, i, x), target)
                if r is not None:
                    cand = (c[a] + r[0], [(a, x)] + r[1])
                    if found is None or (cand[0], len(cand[1]), cand[1]) < (found[0], len(found[1]), found[1]):
                        found = cand
        bc[key] = found
        return found
    out["best_case"] = {}
    for target in TERMINAL:
        r = could(start, target)
        out["best_case"][target] = None if r is None else {"cost": _num(r[0]), "if": [[a, x] for a, x in r[1]]}
    out["proved"] = ("worst_case is the least over all plans (lean/ZPlan.lean: opt_le, opt_attained, optimal); every "
                     "leaf is the judge's own disposition")
    out["markings_judged"] = len(disp)
    return out


def check(claim, marking, costs, tree, hold=()):
    """A plan checked from scratch by the judge: every ground it asks is dirty there and may be asked, every branch
    ends in the disposition written at its leaf, and the worst cost is recomputed. -> {"ok", "worst", "why"}"""
    phi = formalize(claim) if isinstance(claim, str) else claim
    text = _show(phi)
    m = {a: marking.get(a, Z) for a in sorted(_atoms(phi))}
    def walk(node, mm):
        if "verdict" in node:
            d = judge(text, mm)["disposition"]
            if d != node["verdict"] or d not in TERMINAL:
                return None, f"a leaf says {node['verdict']}, the judge says {d}"
            return Fr(0), None
        a = node["check"]
        if mm.get(a) != Z or a in set(hold):
            return None, f"{a!r} is asked where it is not a dirty ground that can be checked"
        if Fr(str(costs[a])) != Fr(node["cost"]):
            return None, f"the plan prices {a!r} at {node['cost']}, the costs say {costs[a]}"
        yes, why = walk(node["if_true"], dict(mm, **{a: T}))
        if yes is None:
            return None, why
        no_, why = walk(node["if_false"], dict(mm, **{a: F}))
        if no_ is None:
            return None, why
        return Fr(str(costs[a])) + max(yes, no_), None
    w, why = walk(tree, m)
    return {"ok": w is not None, "worst": None if w is None else _num(w), "why": why}


def show(tree, indent=0):
    """the plan as a person reads it"""
    pad = "   " * indent
    if "verdict" in tree:
        return f"{pad}-> {tree['verdict']}"
    return (f"{pad}check {tree['check']} (cost {tree['cost']})\n{pad}  if it holds:\n{show(tree['if_true'], indent + 1)}\n"
            f"{pad}  if it fails:\n{show(tree['if_false'], indent + 1)}")
