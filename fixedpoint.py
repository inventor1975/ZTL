# -*- coding: utf-8 -*-
"""
Quarantine as a fixed point (à la Kripke) over ZTL.

A language with a truth predicate: a system of sentences s_i, each
defined by a formula over atoms Tr(s_j) (and constants). The "jump" J
re-evaluates all sentences under the current valuation v. Fixed points
of J are self-consistent valuations; the Z-set of the least point =
quarantine.

Two registers:
  * GREEDY (ZTL): Z evaporates at every operator — the verdict register;
  * LAZY (strong Kleene): Z flows (¬Z=Z etc.) — the grounding register.
Note on the alphabet (preprint §10): the symbol Z is reused
POSITIONALLY — on an input it is the mark ("unverified"), inside the
lazy iteration it plays the solver's phase N ("not yet computed"),
and a phase that never resolves hardens into the quarantine mark.
ZTL splits the role, not the alphabet; what it forbids is promoting
the status to a value of assertions — which is exactly what the
greedy register enforces.

Hypotheses (checked by enumeration, MEASURED):
  H1. The greedy register is non-monotone in the information order
      (Z ⊑ T, Z ⊑ F);
  H2. On the liar (and any odd cycle) the greedy jump has NO fixed
      points — the iteration oscillates (the carousel, formally);
  H3. The lazy jump is monotone and has a least fixed point everywhere
      (Knaster–Tarski), paradoxes receive Z;
  H4. The two-register architecture is mandatory: grounding is lazy,
      verdicts (including the avenger's bullet "content T, no truth")
      are greedy.
"""

from itertools import product

from ztl import T, F, Z, VALUES, OPS2, NOT

# --- the lazy register: strong Kleene ---
def k_not(a):
    return {T: F, F: T, Z: Z}[a]

def k_and(a, b):
    return F if F in (a, b) else (Z if Z in (a, b) else T)

def k_or(a, b):
    return T if T in (a, b) else (Z if Z in (a, b) else F)

def k_imp(a, b):
    return k_or(k_not(a), b)

def k_xor(a, b):
    return Z if Z in (a, b) else (T if a != b else F)

def k_xnor(a, b):
    return Z if Z in (a, b) else (T if a == b else F)

LAZY = {"not": k_not, "and": k_and, "or": k_or,
        "imp": k_imp, "xor": k_xor, "xnor": k_xnor}
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


def least_fp_lazy(system):
    """Least fixed point of the lazy jump (by iteration from Z)."""
    trace, loop = iterate(system, LAZY, steps=64)
    assert loop == len(trace) - 1 or loop is None, "lazy jump cycled?"
    return trace[-1]


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
    print("QUARANTINE AS A FIXED POINT: the greedy and lazy jumps")
    print("=" * 74)

    for title, system in ZOO.items():
        print(f"\n### {title}")

        fps_e = fixed_points(system, EAGER)
        fps_l = fixed_points(system, LAZY)
        print(f"  fixed points of the GREEDY jump: "
              + (", ".join(map(fmt_v, fps_e)) if fps_e else "NONE"))
        print(f"  fixed points of the LAZY jump: "
              + (", ".join(map(fmt_v, fps_l)) if fps_l else "NONE"))

        mw = monotone_witness(system, EAGER)
        ml = monotone_witness(system, LAZY)
        if mw:
            v, w = mw
            print(f"  the greedy jump is NON-monotone: {fmt_v(v)} ⊑ {fmt_v(w)}, "
                  f"but J(v)={fmt_v(jump(system, v, EAGER))} ⋢ "
                  f"J(w)={fmt_v(jump(system, w, EAGER))}")
        if ml:
            print("  !! the lazy jump is non-monotone — contradicts H3")

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

        lfp = least_fp_lazy(system)
        quarantine = [k for k, val in lfp.items() if val == Z]
        print(f"  lazy grounding (least point): {fmt_v(lfp)}"
              + (f"   quarantine: {{{', '.join(quarantine)}}}" if quarantine
                 else "   quarantine empty"))

        # greedy verdict reading on top of the lazy point
        for name in sorted(system):
            content = ev_reg(system[name], lfp, EAGER)
            if lfp[name] == Z:
                bullet = " ← BULLET: content T, no truth" \
                    if content == T else ""
                print(f"    ZTL verdict on the content of {name}: {content}"
                      f" (the sentence itself is quarantined){bullet}")
