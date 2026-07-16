# -*- coding: utf-8 -*-
"""
pengine — the paradox engine. Paradoxes as the range of ONE construction.

The seam (curator's intuition, "a paradox IS an operator"): a self-referential
sentence net is  S_i = f_i(S_1..S_n);  a paradox is what the net DOES, read
operationally.

What the engine MEASURED while cranking (two corrections to the naive story):

  1. The zero-trust GROUNDING (lazy least fixed point) is too COARSE to tell
     paradoxes apart: every pure self-reference (Liar, carousel, every cycle,
     Yablo) grounds uniformly to Z. The discriminator is not the grounding — it
     is the set of CLASSICAL SOLUTIONS of the net (assignments in {T,F} that
     satisfy every S_i = f_i).

  2. For a NEGATION cycle the number of solutions is a parity / graph fact:
        odd  cycle  → 0 solutions → contradictory   (Liar-type)
        even cycle  → 2 solutions → underdetermined  (truth-teller-type)
     i.e. paradoxical ⟺ the reference graph is NOT 2-colourable (not bipartite).
     (This is the graph theory of paradox — Cook, Walicki — reached here by
     measurement, one handle for it.)

So the operational reading: a paradox is a self-referential net whose
fixed-point equations have NO unique classical solution — 0 (over-constrained,
contradictory) or ≥2 (under-constrained, undetermined) — and ZTL then withholds
(grounds to Z) rather than picking.

SCOPE / boundary: this reads FINITE reference nets. Yablo's paradox is
infinitary — any finite truncation is consistent (see boundary()), so the engine
does not reach it; that is exactly where ZTL and classical logic agree. The
genuine step away from classics is on the 0-solution nets: classical logic
EXPLODES (ex falso), ZTL WITHHOLDS (Z, no explosion — the paradox is contained).
Names provisional.
"""

from itertools import product

from ztl import T, F, Z, ev
from fixedpoint import least_fp_lazy, LAZY, ev_reg

HOLE = "S"                                   # the self-reference placeholder


def solutions(net):
    """Classical solutions: assignments in {T,F} with S_i = f_i for all i —
    the fixed points of the reference net. THE discriminator."""
    names = sorted(net)
    out = []
    for combo in product((T, F), repeat=len(names)):
        v = dict(zip(names, combo))
        if all(ev(net[n], v) == v[n] for n in names):
            out.append(v)
    return out


def ground(net):
    """The zero-trust verdict: the lazy least fixed point (cautious — pure
    self-reference lands in Z)."""
    return least_fp_lazy(net)


def lazy_step(net):
    """One lazy (Kleene) jump from all-Z — the first step of grounding.

    THEOREM (measured, 0 violations over all 9015 one-sentence nets ≤6 symbols):
    for a one-sentence net S = f(S), grounding reaches a classical value ⟺ this
    single step already escapes Z, i.e. f evaluated lazily at S=Z is not Z. Proof
    sketch: if the lazy jump sends Z to a classical c, monotonicity gives
    c = jump(Z) ⊑ jump(c), and a classical value is maximal in the information
    order, so jump(c)=c — c is already a fixed point. Grounding is one step.
    The 'cautious Z' nets (unique classical model, yet Z) are exactly those with
    f(Z)=Z: the operator will not propagate a value from ignorance."""
    z = {n: Z for n in net}
    return {n: ev_reg(net[n], z, LAZY) for n in net}


def periods(net):
    """Period spectrum of the greedy jump on {T,F}^n — the DYNAMICAL signature,
    finer than the solution count. Period-1 points ARE the classical solutions;
    the higher periods are the oscillations that separate paradoxes the count
    lumps together (Liar & Curry share [2]; the k-cycle carries 2k)."""
    names = sorted(net)

    def jump(v):
        d = dict(zip(names, v))
        return tuple(ev(net[n], d) for n in names)

    lengths = set()
    for combo in product((T, F), repeat=len(names)):
        v, seen, step = combo, {}, 0
        while v not in seen:
            seen[v] = step
            v = jump(v)
            step += 1
        lengths.add(step - seen[v])
    return sorted(lengths)


def diagnose(net):
    """The operational diagnosis of a reference net — two layers: the classical
    SOLUTIONS (= kernels of the reference graph) and, stricter, the ZTL
    GROUNDING (which also withholds a unique-but-ungrounded answer)."""
    sols = solutions(net)
    g = ground(net)
    n = len(sols)
    grounds_to_value = not any(v == Z for v in g.values())
    if n == 0:
        kind = "contradictory   (0 solutions / no kernel → Z)"
    elif n >= 2:
        kind = f"underdetermined ({n} solutions / many kernels → Z)"
    elif grounds_to_value:
        kind = "determined      (1 solution, grounded → its value)"
    else:
        kind = ("cautious Z      (1 solution exists, but not Kripke-grounded "
                "— ZTL won't grant it)")
    return {"solutions": sols, "ground": g, "n": n,
            "grounds_to_value": grounds_to_value, "kind": kind,
            "periods": periods(net)}


def selfref(f):
    """Convenience for a one-sentence net S = f(S)."""
    return diagnose({HOLE: f})


def all_formulas(max_size):
    """Every formula tree over {S, ⊤, ⊥} with 2..max_size symbols (a symbol =
    one node: a leaf or an operator; compounds only — a bare leaf is not a
    net worth reading). Ops: ¬ and the five binary connectives of the core."""
    by_size = {1: [HOLE, "T", "F"]}
    for n in range(2, max_size + 1):
        acc = [("not", f) for f in by_size[n - 1]]
        for a_sz in range(1, n - 1):
            for a in by_size[a_sz]:
                for b in by_size[n - 1 - a_sz]:
                    acc += [(op, a, b)
                            for op in ("and", "or", "imp", "xor", "xnor")]
        by_size[n] = acc
    return [f for n in range(2, max_size + 1) for f in by_size[n]]


def containment(max_size=6, verbose=True):
    """THE SWEEP behind §11 of the preprint — the numbers cited there are
    recomputed here, not quoted. Over every one-sentence net S = f(S) up to
    `max_size` symbols, two measured claims:

    1. One-step criterion (the theorem at lazy_step): grounding reaches a
       classical value ⟺ one lazy jump from Z escapes Z. Checked per net.
    2. Containment: grounding reaches a classical value only when the net has
       a UNIQUE classical model that is also reachable from ignorance — the
       cautious-Z nets (unique model, yet Z, e.g. S = S∨¬S) witness that
       ZTL-settled nets are a STRICT subset of the classically categorical."""
    pool = all_formulas(max_size)
    agree = boom = cautious = multi = 0
    violations, leaks = [], []
    for f in pool:
        net = {HOLE: f}
        n_sols = len(solutions(net))
        g = ground(net)[HOLE]
        if (g != Z) != (lazy_step(net)[HOLE] != Z):
            violations.append(f)
        if g != Z and n_sols != 1:
            leaks.append(f)              # a ground that is not THE model
        if n_sols == 0:
            boom += 1                    # classical explodes, ZTL contains
        elif n_sols >= 2:
            multi += 1                   # underdetermined for both
        elif g == Z:
            cautious += 1                # unique model, yet ungrounded
        else:
            agree += 1                   # determined: both settle it
    if verbose:
        print(f"CONTAINMENT SWEEP — all {len(pool)} one-sentence nets "
              f"≤{max_size} symbols\n")
        print(f"  one-step grounding criterion:  {len(violations)} violations")
        print(f"  grounded without a unique model: {len(leaks)}")
        print(f"  determined (both settle):      {agree}")
        print(f"  contradictory (0 models → Z):  {boom}")
        print(f"  cautious Z (1 model, still Z): {cautious}   ← the witnesses")
        print(f"  underdetermined (≥2 → Z):      {multi}")
        print("\n  every grounded net has a unique model — ZTL-settled nets "
              "are a strict\n  subset of the classically categorical ones; "
              "the cautious-Z nets (e.g.\n  S=S∨¬S: classically ⊤, here Z) "
              "are the strictness witnesses.")
    return {"n": len(pool), "agree": agree, "boom": boom,
            "cautious": cautious, "multi": multi,
            "violations": violations, "leaks": leaks}


def neg_cycle(k):
    """The k-sentence negation cycle A1=¬A2, …, Ak=¬A1."""
    ns = [f"A{i}" for i in range(1, k + 1)]
    return {ns[i]: ("not", ns[(i + 1) % k]) for i in range(k)}


def yablo(n):
    """Truncated Yablo: Y_i = ∧_{j>i} ¬Y_j, and Y_n = ⊤ (empty conjunction).
    THE BOUNDARY of the engine — see boundary()."""
    net = {}
    for i in range(1, n + 1):
        later = [("not", f"Y{j}") for j in range(i + 1, n + 1)]
        if not later:
            net[f"Y{i}"] = "T"                       # no successors ⇒ vacuously ⊤
        else:
            e = later[0]
            for term in later[1:]:
                e = ("and", e, term)
            net[f"Y{i}"] = e
    return net


# specimens, each a reference net -------------------------------------------
ZOO = {
    "Liar          S=¬S":        {HOLE: ("not", HOLE)},
    "truth-teller  S=S":         {HOLE: HOLE},
    "Curry         S=S→⊥":       {HOLE: ("imp", HOLE, "F")},
    "contra        S=S∧¬S":      {HOLE: ("and", HOLE, ("not", HOLE))},
    "Russell-shadow R∈R↔¬(R∈R)": {HOLE: ("not", HOLE)},
    "carousel      A=B,B=¬A":    {"A": "B", "B": ("not", "A")},
    "even cycle    A=¬B,B=¬A":   {"A": ("not", "B"), "B": ("not", "A")},
}


def report_zoo():
    print("THE ZOO AS reference nets — solutions discriminate, grounding does not\n")
    for name, net in ZOO.items():
        d = diagnose(net)
        gz = "Z (quarantine)" if any(v == Z for v in d["ground"].values()) \
            else ", ".join(f"{k}={v}" for k, v in d["ground"].items())
        print(f"  {name}")
        print(f"      solutions: {d['n']}  →  {d['kind']}")
        print(f"      grounding: {gz}   | dynamics (periods): {d['periods']}\n")


def parity_law():
    print("NEGATION CYCLES — paradoxical ⟺ odd (reference graph not 2-colourable)\n")
    print(f"  {'k':>2} {'#sol':>5} {'ground':>7}   verdict")
    for k in range(1, 7):
        d = diagnose(neg_cycle(k))
        g = "Z" if any(v == Z for v in d["ground"].values()) else "value"
        v = "contradictory (odd)" if d["n"] == 0 else \
            f"{d['n']} solutions (even)"
        print(f"  {k:>2} {d['n']:>5} {g:>7}   {v}")
    print("\n  odd k → 0 solutions (Liar-type); even k → 2 (truth-teller-type);"
          "\n  grounding says Z for all — the STRUCTURE is in the solutions.")


def boundary():
    """The engine's honest LIMIT: Yablo's paradox is infinitary. Any finite
    truncation is CONSISTENT — its last sentence has no successors, so it is
    vacuously ⊤, an anchor that grounds the whole chain. So truncation ≠
    paradox, and the engine (finite reference nets) does not reach Yablo. This
    is exactly where ZTL and classical logic COINCIDE (both: consistent)."""
    print("BOUNDARY — truncated Yablo is CONSISTENT (the engine can't reach the "
          "real, infinitary Yablo)\n")
    print(f"  {'N':>2} {'#sol':>5}   unique solution")
    for n in range(3, 7):
        d = diagnose(yablo(n))
        sol = d["solutions"][0] if d["n"] == 1 else "(not unique!)"
        print(f"  {n:>2} {d['n']:>5}   {sol}")
    print("\n  1 solution (not 0) — the vacuous ⊤ bottom anchors it. The Yablo "
          "paradox\n  needs NO bottom (infinite forward chain); finite "
          "truncation trivialises it.")


if __name__ == "__main__":
    report_zoo()
    print("=" * 64 + "\n")
    containment()
    print("\n" + "=" * 64 + "\n")
    parity_law()
    print("\n" + "=" * 64 + "\n")
    boundary()
