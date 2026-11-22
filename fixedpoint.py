# -*- coding: utf-8 -*-
"""
Quarantine as a fixed point (à la Kripke) over ZTL — PURE BRANCH (curator 2026-11-22: only ZTL).

A language with a truth predicate: a system of sentences s_i, each defined by a formula over atoms Tr(s_j)
(and constants). The jump J re-evaluates all sentences under the current valuation v; the least fixed point,
reached by iterating from "nothing determined", leaves the quarantine undetermined.

Two registers, both ZTL:
  * GREEDY (ZTL's tables): Z evaporates at every operator — the verdict register;
  * STABLE (the grounding step, Lean ZGround): an OWN sentence not yet determined is in the solver's phase N
    ("not yet computed", never a truth value); it becomes T (F) when its definition is T (F) — by ZTL's
    tables, a FOREIGN input read as the mark Z — under EVERY classical value of the still-undetermined own
    sentences (one value per sentence: IF STABLE). No strong Kleene table, no ¬Z = Z.

Hypotheses (checked by enumeration, MEASURED; H3 proved in Lean ZGround.evalS_mono / kt_fixed):
  H1. The greedy register is non-monotone in the information order (Z ⊑ T, Z ⊑ F);
  H2. On the liar (and any odd cycle) the greedy jump has NO fixed points — the iteration oscillates;
  H3. The stable jump is monotone and has a least fixed point everywhere (Knaster–Tarski); paradoxes stay N;
  H4. Grounding is the stable step, verdicts are greedy — both from ZTL alone.
"""

from itertools import product

from ztl import T, F, Z, VALUES, OPS2, NOT
from zread import stable

from zread import N  # the solver's phase: an own sentence not yet determined (never a truth value)
EAGER = {"not": NOT, **OPS2}


def ev_reg(phi, v, ops):
    """Value of a formula under valuation v (sentence name -> value)."""
    if isinstance(phi, str):
        return phi if phi in VALUES else v[phi]   # constant or Tr(name)
    op = phi[0]
    if op == "not":
        return ops["not"](ev_reg(phi[1], v, ops))
    return ops[op](ev_reg(phi[1], v, ops), ev_reg(phi[2], v, ops))


def jump(system, v, ops):
    return {name: ev_reg(defn, v, ops) for name, defn in system.items()}


def fixed_points(system, ops):
    names = sorted(system)
    result = []
    for combo in product(VALUES, repeat=len(names)):
        v = dict(zip(names, combo))
        if jump(system, v, ops) == v:
            result.append(v)
    return result


def leq_info(a, b):
    """Information order: Z ⊑ everything, T and F incomparable."""
    return a == b or a == Z


def v_leq(v, w):
    return all(leq_info(v[k], w[k]) for k in v)


def monotone_witness(system, ops):
    """A pair of valuations v ⊑ w with J(v) ⋢ J(w), if one exists."""
    names = sorted(system)
    vals = [dict(zip(names, c)) for c in product(VALUES, repeat=len(names))]
    for v in vals:
        for w in vals:
            if v_leq(v, w) and not v_leq(jump(system, v, ops),
                                         jump(system, w, ops)):
                return v, w
    return None


def iterate(system, ops, steps=12):
    """Iterate the jump from all-Z; tail of the trajectory."""
    v = {name: Z for name in system}
    trace = [v]
    for _ in range(steps):
        v = jump(system, v, ops)
        if v in trace:
            i = trace.index(v)
            return trace, i          # cycle: trace[i:] repeats
        trace.append(v)
    return trace, None


def _names(phi, acc):
    if isinstance(phi, str):
        if phi not in VALUES:
            acc.add(phi)
    else:
        for x in phi[1:]:
            _names(x, acc)
    return acc


def stable_eval(phi, v, system):
    """The STABLE step for one definition — classics first, decided in ONE place (`zread.stable`): T (F) if
    the definition is classically true (false) under every classical value of every open atom, own sentence
    at N or foreign input at Z; otherwise N. ZTL's tables give the verdict, not the grounding."""
    return stable(phi, v)


def jump_stable(system, v):
    """Re-evaluate EVERY own definition (as Lean's jumpS does); inputs stay the mark Z."""
    return {s: (Z if system[s] == Z else stable_eval(system[s], v, system)) for s in system}


def least_fp_stable(system):
    """Least fixed point of the stable jump, from 'nothing determined' (inputs Z, own sentences N)."""
    v = {s: (Z if system[s] == Z else N) for s in system}
    while True:
        w = jump_stable(system, v)
        if w == v:
            return v
        v = w


def stable_monotone_witness(system):
    """A pair v ⊑ w (own sentences over N/T/F, inputs Z) with J(v) ⋢ J(w), if one exists."""
    own = sorted(s for s in system if system[s] != Z)
    base = {s: Z for s in system if system[s] == Z}
    vals = [{**base, **dict(zip(own, c))} for c in product((N, T, F), repeat=len(own))]
    le = lambda a, b: a == b or a == N
    for v in vals:
        for w in vals:
            if all(le(v[k], w[k]) for k in own):
                jv, jw = jump_stable(system, v), jump_stable(system, w)
                if not all(le(jv[k], jw[k]) for k in own):
                    return v, w
    return None


# --- the zoo of systems ---
ZOO = {
    "liar            λ: ¬Tr(λ)": {
        "λ": ("not", "λ")},
    "truth-teller    τ: Tr(τ)": {
        "τ": "τ"},
    "carousel        A: Tr(B); B: ¬Tr(A)": {
        "A": "B", "B": ("not", "A")},
    "even cycle      A: ¬Tr(B); B: ¬Tr(A)": {
        "A": ("not", "B"), "B": ("not", "A")},
    "grounded        g0: T; g1: Tr(g0); g2: ¬Tr(g1)∨Tr(g0)": {
        "g0": "T", "g1": "g0", "g2": ("or", ("not", "g1"), "g0")},
    "avenger         μ: ¬Tr(μ) ∨ ¬(Tr(μ)↔Tr(μ))": {
        "μ": ("or", ("not", "μ"), ("not", ("xnor", "μ", "μ")))},
}


def fmt_v(v):
    return "{" + ", ".join(f"{k}={v[k]}" for k in sorted(v)) + "}"


if __name__ == "__main__":
    print("=" * 74)
    print("QUARANTINE AS A FIXED POINT: the greedy jump and the stable step")
    print("=" * 74)

    for title, system in ZOO.items():
        print(f"\n### {title}")

        fps_e = fixed_points(system, EAGER)
        print(f"  fixed points of the GREEDY jump: "
              + (", ".join(map(fmt_v, fps_e)) if fps_e else "NONE"))

        mw = monotone_witness(system, EAGER)
        ml = stable_monotone_witness(system)
        if mw:
            v, w = mw
            print(f"  the greedy jump is NON-monotone: {fmt_v(v)} ⊑ {fmt_v(w)}, "
                  f"but J(v)={fmt_v(jump(system, v, EAGER))} ⋢ "
                  f"J(w)={fmt_v(jump(system, w, EAGER))}")
        if ml:
            print("  !! the stable step is non-monotone — contradicts H3")

        trace, loop = iterate(system, EAGER)
        if loop is None:
            print("  greedy iteration from Z: did not converge within the limit")
        else:
            period = len(trace) - loop
            if period == 1:
                print(f"  greedy iteration from Z: converged to {fmt_v(trace[-1])}")
            else:
                cyc = trace[loop:]
                print(f"  greedy iteration from Z: CYCLE of period {period}: "
                      + " → ".join(fmt_v(x) for x in cyc))

        lfp = least_fp_stable(system)
        quarantine = [k for k, val in lfp.items() if val == N]
        print(f"  stable grounding (least point): {fmt_v(lfp)}"
              + (f"   quarantine: {{{', '.join(quarantine)}}}" if quarantine
                 else "   quarantine empty"))

        # greedy verdict reading on top of the stable point
        for name in sorted(system):
            # after the fixed point a phase that never resolved hardens into the quarantine mark Z (SPEC §N)
            content = ev_reg(system[name], {k: (Z if x == N else x) for k, x in lfp.items()}, EAGER)
            if lfp[name] == N:
                bullet = " ← BULLET: content T, no truth" \
                    if content == T else ""
                print(f"    ZTL verdict on the content of {name}: {content}"
                      f" (the sentence itself is quarantined){bullet}")
