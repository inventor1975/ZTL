# -*- coding: utf-8 -*-
"""
Expedition E18: the quarantine passport — kinds of ungroundedness.

Z was blind: the liar and the truth-teller both landed in quarantine
with the same mark. The passport cures the blindness WITHOUT touching
the logic: verdicts stay T/F, the tables and greediness are intact —
the passport is solver-side metadata about the quarantine set, computed
per strongly connected component of the dependency graph:

  GROUNDED         lazy lfp gives a classical value — no passport needed.
  PARADOX          the component has NO classical model consistent with
                   its grounded environment (odd cycles): the refusal is
                   PERMANENT — no act can ever lift it; the greedy
                   oscillation period is recorded (liar 2, carousel 4).
  UNDERDETERMINED  classical models exist (≥ 2): the refusal stands
                   UNTIL STIPULATION — an external choice grounds it.
  INPUT            a plain unverified input imported into the system:
                   the refusal stands until verification (E12).
  DOWNSTREAM       inherited quarantine: the component itself is fine,
                   but it reads quarantined sentences below; culprits
                   are listed — the provenance of refusal (E7 again).

Operational meaning (the stipulation theorem, MEASURED):
UNDERDETERMINED ⟺ stipulating any of its classical models grounds the
component and disturbs nothing already grounded; PARADOX ⟺ every
stipulation contradicts the component's own definitions. The E12 pair
(value, warranty) extends to refusals: quarantine = (Z, passport).

Kripke's taxonomy (grounded/paradoxical/intrinsically ungrounded) and
the revision-theoretic oscillation signatures (Gupta–Belnap), here as
a computable instrument over finite systems.
"""

from itertools import product

from ztl import T, F, Z, VALUES
from fixedpoint import EAGER, LAZY, jump, ev_reg, least_fp_lazy, fmt_v


# ------------------------------------------------------ dependency graph
def deps(phi, acc=None):
    if acc is None:
        acc = set()
    if isinstance(phi, str):
        if phi not in VALUES:
            acc.add(phi)
    else:
        for part in phi[1:]:
            deps(part, acc)
    return acc


def sccs(system):
    """Tarjan (iterative). Emits components dependencies-first."""
    graph = {s: sorted(deps(d) & set(system)) for s, d in system.items()}
    index, low, on_stack = {}, {}, set()
    stack, out, counter = [], [], [0]

    def strongconnect(v0):
        work = [(v0, 0)]
        while work:
            v, i = work.pop()
            if i == 0:
                index[v] = low[v] = counter[0]
                counter[0] += 1
                stack.append(v)
                on_stack.add(v)
            recurse = False
            for j in range(i, len(graph[v])):
                w = graph[v][j]
                if w not in index:
                    work.append((v, j + 1))
                    work.append((w, 0))
                    recurse = True
                    break
                if w in on_stack:
                    low[v] = min(low[v], index[w])
            if recurse:
                continue
            if low[v] == index[v]:
                comp = []
                while True:
                    w = stack.pop()
                    on_stack.discard(w)
                    comp.append(w)
                    if w == v:
                        break
                out.append(sorted(comp))
            if work:
                parent = work[-1][0]
                low[parent] = min(low[parent], low[v])

    for v in sorted(system):
        if v not in index:
            strongconnect(v)
    return out


# ------------------------------------------------------------- passports
def component_models(comp, system, env):
    """Classical assignments to comp that are fixed points of its jump
    given the (classical) environment env."""
    models = []
    for combo in product((T, F), repeat=len(comp)):
        vc = dict(zip(comp, combo))
        full = {**env, **vc}
        if all(ev_reg(system[s], full, EAGER) == vc[s] for s in comp):
            models.append(vc)
    return models


def oscillation_period(comp, system, env, steps=32):
    v = {s: Z for s in comp}
    trace = [v]
    for _ in range(steps):
        v = {s: ev_reg(system[s], {**env, **v}, EAGER) for s in comp}
        if v in trace:
            return len(trace) - trace.index(v)
        trace.append(v)
    return None


def passports(system):
    """Passport per component; returns (lfp, list of reports)."""
    lfp = least_fp_lazy(system)
    comp_kind = {}
    reports = []
    for comp in sccs(system):
        names = set(comp)
        if all(lfp[s] in (T, F) for s in comp):
            for s in comp:
                comp_kind[s] = ("GROUNDED", None)
            continue
        env_names = set()
        for s in comp:
            env_names |= deps(system[s]) - names
        env = {n: lfp[n] for n in env_names}
        if any(v == Z for v in env.values()):
            culprits = sorted({n for n in env_names if lfp[n] == Z})
            permanent = any(comp_kind[c][0] in ("PARADOX",)
                            or (comp_kind[c][0] == "DOWNSTREAM"
                                and comp_kind[c][1] == "permanent")
                            for c in culprits)
            kind = ("DOWNSTREAM", "permanent" if permanent else "conditional")
            reports.append((comp, kind[0],
                            f"culprits {culprits}, refusal {kind[1]}"))
        else:
            self_ref = any(names & deps(system[s]) for s in comp)
            if not self_ref and len(comp) == 1:
                kind = ("INPUT", None)
                reports.append((comp, "INPUT",
                                "unverified input; refusal until verification"))
            else:
                models = component_models(comp, system, env)
                if models:
                    kind = ("UNDERDETERMINED", len(models))
                    reports.append((comp, "UNDERDETERMINED",
                                    f"{len(models)} classical models; "
                                    f"refusal until stipulation"))
                else:
                    p = oscillation_period(comp, system, env)
                    kind = ("PARADOX", p)
                    reports.append((comp, "PARADOX",
                                    f"no classical models; oscillation "
                                    f"period {p}; refusal PERMANENT"))
        for s in comp:
            comp_kind[s] = kind
    return lfp, reports, comp_kind


# ------------------------------------------------ the stipulation theorem
def stipulate(system, choice):
    """Replace the chosen sentences' definitions by constants."""
    return {s: (choice[s] if s in choice else d) for s, d in system.items()}


def stipulation_theorem(system):
    """UNDERDETERMINED components: every classical model, once stipulated,
    grounds the component and never disturbs the grounded part.
    PARADOX components: every stipulation contradicts a definition."""
    lfp, reports, _ = passports(system)
    grounded_before = {s: v for s, v in lfp.items() if v in (T, F)}
    ok_under = checked_under = 0
    ok_par = checked_par = 0
    for comp, kind, _ in reports:
        names = set(comp)
        env_names = set()
        for s in comp:
            env_names |= deps(system[s]) - names
        env = {n: lfp[n] for n in env_names}
        if kind == "UNDERDETERMINED":
            for m in component_models(comp, system, env):
                checked_under += 1
                lfp2 = least_fp_lazy(stipulate(system, m))
                if all(lfp2[s] == m[s] for s in comp) and \
                   all(lfp2[s] == v for s, v in grounded_before.items()):
                    ok_under += 1
        elif kind == "PARADOX":
            for combo in product((T, F), repeat=len(comp)):
                vc = dict(zip(comp, combo))
                checked_par += 1
                full = {**env, **vc}
                if any(ev_reg(system[s], full, EAGER) != vc[s]
                       for s in comp):
                    ok_par += 1     # the decree contradicts a definition
    return ok_under, checked_under, ok_par, checked_par


# ------------------------------------------------------------------ zoos
MIXED = {
    "λ":  ("not", "λ"),                       # liar — paradox, period 2
    "τ":  "τ",                                # truth-teller — 2 models
    "A":  "B", "B": ("not", "A"),             # carousel — paradox, period 4
    "E1": ("not", "E2"), "E2": ("not", "E1"),  # even cycle — 2 models
    "m":  "Z",                                # unverified input
    "g0": "T",                                # grounded
    "g1": ("not", "λ"),                       # downstream of the liar
    "g2": ("or", "E1", ("not", "E1")),        # downstream of a choice
    "g3": ("or", "g0", "g0"),                 # grounded via g0
}

RUSSELL = {}
for x in ("a", "b", "R"):
    RUSSELL[f"{x}∈a"] = "F"
    RUSSELL[f"{x}∈b"] = "T" if x == "b" else "F"
    RUSSELL[f"{x}∈R"] = ("not", f"{x}∈{x}")


def cycle_system(pattern):
    n = len(pattern)
    return {f"s{i}": (("not", f"s{(i + 1) % n}") if inv else f"s{(i + 1) % n}")
            for i, inv in enumerate(pattern)}


if __name__ == "__main__":
    print("=" * 72)
    print("E18. THE QUARANTINE PASSPORT: WHY REFUSED, AND IS IT LIFTABLE")
    print("=" * 72)

    print("\n### The mixed zoo: one system, every kind at once")
    lfp, reports, kinds = passports(MIXED)
    grounded = sorted(s for s, v in lfp.items() if v in (T, F))
    print(f"  grounded (no passport needed): {grounded}")
    for comp, kind, detail in reports:
        print(f"  {str(comp):14s} {kind:15s} {detail}")
    print("  Verdicts and tables untouched: the passport lives in the")
    print("  solver's report — the grounded part is exactly the E9-lfp.")

    print("\n### The stipulation theorem (operational meaning of the kinds)")
    ou, cu, op_, cp = stipulation_theorem(MIXED)
    print(f"  UNDERDETERMINED: stipulations grounding cleanly: {ou} of {cu}")
    print(f"  PARADOX: decrees contradicting their own definitions: "
          f"{op_} of {cp}")
    both = ou == cu and op_ == cp and cu > 0 and cp > 0
    print(f"  {'✓ STIPULATION THEOREM: total' if both else '✗ FAILED'} — "
          f"underdetermined ⟺ liftable by choice, paradox ⟺ permanent")

    print("\n### Parity cross-check (E2 through the passport)")
    good = bad = 0
    for n in range(1, 6):
        for pattern in product((0, 1), repeat=n):
            sysc = cycle_system(pattern)
            _, reps, _ = passports(sysc)
            kind = reps[0][1] if reps else "GROUNDED"
            expect = "PARADOX" if sum(pattern) % 2 else "UNDERDETERMINED"
            if reps and kind == expect:
                good += 1
            elif not reps and sum(pattern) % 2 == 0:
                good += 1    # fully grounded even cycle (no inversions...)
            else:
                bad += 1
                print(f"  ✗ n={n} pattern={pattern}: {kind}")
    print(f"  cycles 1–5, all patterns: parity cross-check: {good} of "
          f"{good + bad} ✓" if bad == 0 else f"  ✗ mismatches: {bad}")

    print("\n### Russell under the passport")
    lfpR, repsR, _ = passports(RUSSELL)
    for comp, kind, detail in repsR:
        print(f"  {str(comp):14s} {kind:15s} {detail}")
    print(f"  grounded facts: "
          f"{sorted(s for s, v in lfpR.items() if v in (T, F))}")
    lfpS, repsS, _ = passports({"S∈S": "S∈S"})
    for comp, kind, detail in repsS:
        print(f"  twin {str(comp):9s} {kind:15s} {detail}")

    print("\n### Honest caveats")
    print("  Yablo stays invisible: every finite truncation is grounded")
    print("  (E3) — the passport of infinite regress needs an infinite")
    print("  instrument; recorded as a limitation, not silently ignored.")
    print("  Refusal classes now mirror E12: INPUT — until verification;")
    print("  UNDERDETERMINED — until stipulation; PARADOX/DOWNSTREAM-of-")
    print("  paradox — permanent. Quarantine = (Z, passport).")
    if not both or bad:
        raise SystemExit("PASSPORT MEASUREMENT FAILED — stop.")
