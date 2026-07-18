# -*- coding: utf-8 -*-
"""
Expedition E24: logical time — the verification tree and the grade automaton.

THE WORD-SPEC (agreed 2026-07-18, "logic below, time on top"). ZTL has no
physical clock and stays blind to duration; its only clock is the ARRIVAL
OF GROUND: one tick = one act verify(mark → earned value) (zverify.py).
A moment = a marking; the past = the verified prefix; the future = the
TREE of possible verifications (each remaining Z can resolve either way —
branching time, not a line; "everyone's time differs" = different traces
through one tree).

THE CENTRAL IDENTIFICATION — the E12/E21 warranty ladder IS a temporal
logic that was never named as one:

    until-verification  =  true NOW            (present tense, credit)
    sound               =  true AT EVERY ENDING (all completed traces
                           agree; the road may wobble)
    hereditary          =  true ALWAYS ALONG EVERY PATH (invariant of
                           the whole tree; never revoked)

Three grades = three temporal quantifiers: now / at-all-endings /
always-on-all-paths. E10 (zmodal: worlds = completions) is the STATICS
of this structure; this stand is its DYNAMICS — the paths through the
partial refinements between here and the completions.

WHAT IS MEASURED (the grade automaton, states = (verdict, grade)):
  1. All transitions (v,g) → (v',g') under a single tick, exhaustively
     on all depth-≤2 formulas over two atoms — the transition matrix,
     the empty cells, and the automaton laws:
       * (v, hereditary) is ABSORBING — no tick changes value or grade
         (E12 §4 re-read as a temporal law: hereditary = AG-invariance);
       * Z-valued states occur ONLY at bare atoms (greediness in
         temporal costume: no compound state ever waits).
  2. Full-trace trajectories (curated pool incl. the E21 cells and the
     4-atom trophy): every completed trace ENDS hereditary — the arrow
     of logical time points at the shelf; strict full ladder
     U→S→H within one trace; demotions (S→U: credit worsens before it
     settles); value flips mid-road.
  3. EARLY SETTLEMENT: verdicts that become hereditary while marks
     remain (or(p,q) at p:=T no longer cares about q) — ground can
     arrive before all the ground.
  4. Settling time: min/max ticks-to-hereditary per formula — how much
     verification a verdict needs before it is shelf-stable.

MEASURED (this file, deterministic, re-run to reproduce):
  automaton (2 atoms, depth ≤2 exhaustive): 2,906 formulas, 29,812
  ticks; hereditary absorbing: 0 violations; compound formulas caught
  waiting (value Z): 0; U→H direct jump EXISTS (14,818 — ground can
  arrive all at once); S→U demotion EXISTS (108); the S-columns of the
  matrix are EMPTY.
  traces (curated + trophy): 130 completed traces, ALL 130 end
  hereditary — the arrow of logical time; strict full ladder U→S→H:
  0 traces; genuine entries into sound-only at t≥1: 0; S→U demotions
  on the road: 4; verdict flips mid-trace: 58; early settlement: 68 of
  130 traces; settling 0/1 exists (¬(p∧¬p) is born hereditary),
  xor/xnor need every mark (2/2).
  THE E24 STORY — a conjecture born and killed the same day, in the
  open (§5–§6). The corrected hunt (§5; the naive sweep counted
  irrelevant-tick S→S as entries — fixed) found 0 genuine entries into
  sound-only on 13,059 formulas × 78,354 ticks, and for half an hour
  the conjecture stood: "sound is a BIRTH grade, never earned by a
  tick". The PROOF ATTEMPT then broke at a specific spot, and the spot
  folded into a COUNTEREXAMPLE (§6): the hunts were SHALLOW (depth ≤2),
  while the insured E21 shape lives at depth 3. The selector
      φ = (a ∧ X) ∨ (¬a ∧ p),   X = ¬¬p ∨ (q ∨ ¬q)
  at all-marked start walks  F/U → (a:=T) → T/S → (p:=T) → T/H:
  a GENUINE entry into sound-only AND the full strict ladder U→S→H,
  both realized. Verifying the SELECTOR atom routes the formula onto
  the insured branch, and soundness is EARNED. So: sound can be earned
  by the tick that verifies WHICH WORLD YOU ARE IN; the §5 zeros were
  a pool artifact, kept as the honest record of how the conjecture
  died.

HONEST BOUNDARY. This is not LTL3 re-derived: LTL3 grades one "?"
about trace membership on a finite prefix; here the evolving object is
the WARRANTY GRADE of a verdict over the refinement tree, and the
grades themselves are the temporal quantifiers. Physical time, duration,
"how long between ticks" — still outside ZTL's axis, by design (the
essay seed "N = logical time" is IDEAS #11; this stand is its formal
shadow, no philosophy claimed).
"""

from itertools import permutations, product

from ztl import T, F, Z, OPS2, atoms
from zmodal import ztl_eval
from zverify import verify, hereditary_bit, stable_bit, grade

GRADES = {"until-verification": "U", "sound": "S", "hereditary": "H"}


def gstate(phi, m):
    """The automaton state of a verdict: (value, grade-letter)."""
    return (ztl_eval(phi, m), GRADES[grade(phi, m)])


# ------------------------------------------------------------ formula pools
def depth2_pool():
    """Exhaustive formulas of depth ≤ 2 over atoms p, q."""
    d0 = ["p", "q"]
    d1 = [("not", a) for a in d0] + \
         [(op, a, b) for op in OPS2 for a in d0 for b in d0]
    base = d0 + d1
    d2 = [("not", f) for f in d1] + \
         [(op, a, b) for op in OPS2 for a in base for b in base]
    seen, pool = set(), []
    for f in d0 + d1 + d2:
        if f not in seen:
            seen.add(f)
            pool.append(f)
    return pool


def curated_pool():
    """The E12 pool + the E21 cells + the 4-atom trophy (rich trajectories)."""
    p, q = "p", "q"
    pool = [p, ("not", p), ("or", p, ("not", p)), ("not", ("not", p)),
            ("imp", p, q), ("and", p, ("not", q)), ("xnor", p, q),
            ("or", ("and", p, q), ("not", p)), ("xor", p, ("not", q)),
            ("imp", ("not", ("not", p)), q),
            ("or", ("not", ("not", p)), ("or", q, ("not", q))),   # E21 cell
            ("imp", ("not", p), ("imp", q, q)),                   # simpler cell
            ("or", p, q),                                         # early settler
            ("not", ("and", p, ("not", p)))]                      # born hereditary
    trophy = ("imp", ("xnor", "d", ("not", "c")),
              ("imp", ("imp", "b", "a"), ("xnor", "b", "c")))     # E12 §5
    return pool, trophy


def markings_for(phi):
    names = sorted(atoms(phi))
    for combo in product((T, F, "M"), repeat=len(names)):
        yield dict(zip(names, combo))


# ------------------------------------------------------- 1. the automaton
def automaton(pool):
    trans = {}
    n_ticks = 0
    her_broken = 0            # ticks that leave a hereditary state
    z_compound = 0            # compound formulas caught waiting (value Z)
    for phi in pool:
        compound = not isinstance(phi, str)
        for m in markings_for(phi):
            marks = [a for a, s in m.items() if s == "M"]
            if not marks:
                continue
            s1 = gstate(phi, m)
            if compound and s1[0] == Z:
                z_compound += 1
            for a in marks:
                for val in (T, F):
                    s2 = gstate(phi, verify(m, a, val))
                    trans[(s1, s2)] = trans.get((s1, s2), 0) + 1
                    n_ticks += 1
                    if s1[1] == "H" and s2 != s1:
                        her_broken += 1
    return trans, n_ticks, her_broken, z_compound


# ------------------------------------------------------ 2. full traces
def traces(phi, m0):
    """All completed verification traces from m0: sequences of gstates."""
    marks = sorted(a for a, s in m0.items() if s == "M")
    out = []
    for order in permutations(marks):
        for vals in product((T, F), repeat=len(marks)):
            m, states = dict(m0), [gstate(phi, m0)]
            for a, v in zip(order, vals):
                m = verify(m, a, v)
                states.append(gstate(phi, m))
            out.append(states)
    return out


def trace_stats(pool_and_trophy):
    pool, trophy = pool_and_trophy
    all_formulas = pool + [trophy]
    n_traces = end_H = ladder = demote = flips = early = entered_S = 0
    ladder_ex = demote_ex = early_ex = entered_S_ex = None
    settle = {}
    for phi in all_formulas:
        m0 = {a: "M" for a in sorted(atoms(phi))}
        if phi == trophy:
            m0["a"] = F                      # the E12 §5 cell
        k = sum(1 for s in m0.values() if s == "M")
        best = k
        for tr in traces(phi, m0):
            n_traces += 1
            gs = [g for _, g in tr]
            vs = [v for v, _ in tr]
            end_H += (gs[-1] == "H")
            # first tick where the verdict is already hereditary
            first_H = next(i for i, g in enumerate(gs) if g == "H")
            best = min(best, first_H)
            if first_H < k:
                early += 1
                if early_ex is None and first_H > 0:
                    early_ex = (phi, tr)
            if "U" in gs and "S" in gs and "H" in gs and \
                    gs.index("U") < gs.index("S") < gs.index("H"):
                ladder += 1
                ladder_ex = ladder_ex or (phi, tr)
            enter_S = sum(1 for g in gs[1:] if g == "S")
            if enter_S:
                entered_S += enter_S
                entered_S_ex = entered_S_ex or (phi, tr)
            for g1, g2 in zip(gs, gs[1:]):
                if g1 == "S" and g2 == "U":
                    demote += 1
                    demote_ex = demote_ex or (phi, tr)
            flips += sum(1 for v1, v2 in zip(vs, vs[1:])
                         if v1 != v2 and Z not in (v1, v2))
        settle[str(phi)] = (best, k)
    return dict(n=n_traces, end_H=end_H, ladder=ladder, ladder_ex=ladder_ex,
                demote=demote, demote_ex=demote_ex, flips=flips,
                early=early, early_ex=early_ex, settle=settle,
                entered_S=entered_S, entered_S_ex=entered_S_ex)


def show_state(s):
    return f"{s[0]}/{s[1]}"


if __name__ == "__main__":
    print("=" * 72)
    print("E24. LOGICAL TIME: the verification tree and the grade automaton")
    print("     (time = the arrival of ground; the ladder = temporal quantifiers)")
    print("=" * 72)

    # ---- 1. the automaton, exhaustive depth ≤ 2 -------------------------
    pool = depth2_pool()
    trans, n_ticks, her_broken, z_compound = automaton(pool)
    states = sorted({s for pair in trans for s in pair})
    print(f"\n### 1. The grade automaton (exhaustive depth ≤ 2 over p,q)")
    print(f"  formulas: {len(pool)}; ticks measured: {n_ticks}")
    print(f"  states seen: {', '.join(show_state(s) for s in states)}")
    print("  transition counts (rows = from, cols = to):")
    header = "        " + " ".join(f"{show_state(s):>7s}" for s in states)
    print(header)
    for s1 in states:
        row = [f"{trans.get((s1, s2), 0):7d}" for s2 in states]
        print(f"  {show_state(s1):>5s} " + " ".join(row))
    print(f"  hereditary ABSORBING — ticks leaving an H-state: {her_broken} "
          f"(must be 0)")
    print(f"  compound formulas caught waiting (value Z): {z_compound} "
          f"(must be 0 — greediness in temporal costume)")
    assert her_broken == 0 and z_compound == 0
    u_to_h = sum(c for (s1, s2), c in trans.items()
                 if s1[1] == "U" and s2[1] == "H")
    s_to_u = sum(c for (s1, s2), c in trans.items()
                 if s1[1] == "S" and s2[1] == "U")
    print(f"  U→H direct jumps: {u_to_h} (ground can arrive all at once)")
    print(f"  S→U demotions:    {s_to_u} (credit can worsen before it settles)")
    assert u_to_h > 0 and s_to_u > 0

    # ---- 2. trajectories along completed traces ------------------------
    st = trace_stats(curated_pool())
    print(f"\n### 2. Completed traces (curated pool + the 4-atom trophy)")
    print(f"  traces walked: {st['n']}; ending hereditary: {st['end_H']} "
          f"(must be all — the arrow of logical time)")
    assert st['end_H'] == st['n']
    print(f"  strict full ladder U→S→H within one trace: {st['ladder']} traces")
    if st['ladder_ex']:
        phi, tr = st['ladder_ex']
        print(f"    e.g. {phi}: " +
              " → ".join(show_state(s) for s in tr))
    print(f"  ticks ENTERING a sound-only state (t≥1, incl. 3-mark trophy): "
          f"{st['entered_S']}")
    if st['entered_S_ex']:
        phi, tr = st['entered_S_ex']
        print(f"    e.g. {phi}: " +
              " → ".join(show_state(s) for s in tr))
    else:
        print("    none on THIS pool (with one mark left, sound ⟺ hereditary")
        print("    by arithmetic; the 3-mark trophy did not enter S either) —")
        print("    but see §6: the entry EXISTS at depth 4.")
    print(f"  S→U demotions on the road: {st['demote']}")
    if st['demote_ex']:
        phi, tr = st['demote_ex']
        print(f"    e.g. {phi}: " +
              " → ".join(show_state(s) for s in tr))
    print(f"  verdict flips mid-trace (classical→classical): {st['flips']}")

    # ---- 3. early settlement -------------------------------------------
    print(f"\n### 3. Early settlement — hereditary BEFORE the last mark")
    print(f"  traces settling early: {st['early']} of {st['n']}")
    if st['early_ex']:
        phi, tr = st['early_ex']
        print(f"    e.g. {phi}: " +
              " → ".join(show_state(s) for s in tr) +
              "   (marks remained, verdict already shelf-stable)")
    assert st['early'] > 0

    # ---- 4. settling time ----------------------------------------------
    print(f"\n### 4. Settling time (best-case ticks to hereditary / marks)")
    for name, (best, k) in sorted(st['settle'].items(),
                                  key=lambda kv: (kv[1][0], kv[0])):
        print(f"  {best}/{k}  {name}")
    # ---- 5. the hunt: can sound-only be ENTERED at all? -----------------
    print(f"\n### 5. The hunt: is sound-only ever EARNED by a tick?")
    print("  (3 atoms, depth ≤ 2 exhaustive, start = all three marked;")
    print("   the naive count is corrected — an irrelevant tick keeping an")
    print("   already-sound state S→S is NOT an entry)")
    d0 = ["p", "q", "r"]
    d1 = [("not", a) for a in d0] + \
         [(op, a, b) for op in OPS2 for a in d0 for b in d0]
    base3 = d0 + d1
    d2 = [("not", f) for f in d1] + \
         [(op, a, b) for op in OPS2 for a in base3 for b in base3]
    pool3 = list(dict.fromkeys(d0 + d1 + d2))
    m0 = {"p": "M", "q": "M", "r": "M"}
    hunt_ticks = genuine = 0
    for phi in pool3:
        g0 = gstate(phi, m0)[1]
        for a in d0:
            for val in (T, F):
                hunt_ticks += 1
                g1 = gstate(phi, verify(m0, a, val))[1]
                if g1 == "S" and g0 != "S":
                    genuine += 1
    print(f"  formulas: {len(pool3)}; ticks: {hunt_ticks}")
    print(f"  GENUINE entries into sound-only (predecessor not S): {genuine}")
    assert genuine == 0
    print("  → on THIS pool: none. For half an hour this stood as the")
    print("    conjecture 'sound is a birth grade'. It is FALSE — the pool")
    print("    was shallow (depth ≤2); the refutation is §6.")

    # ---- 6. the refutation: sound IS earned, by the selector ------------
    print(f"\n### 6. The refutation — the selector witness (depth 4)")
    print("  φ = (a ∧ X) ∨ (¬a ∧ p),  X = ¬¬p ∨ (q ∨ ¬q)  (the E21 insured cell)")
    Xf = ("or", ("not", ("not", "p")), ("or", "q", ("not", "q")))
    phi_w = ("or", ("and", "a", Xf), ("and", ("not", "a"), "p"))
    w0 = {"a": "M", "p": "M", "q": "M"}
    w1 = verify(w0, "a", T)
    w2 = verify(w1, "p", T)
    path = [("all marked", w0), ("a:=T", w1), ("p:=T", w2)]
    gs = []
    for label, m in path:
        v, g = gstate(phi_w, m)
        gs.append(g)
        print(f"    {label:12s} verdict {v}  grade {g}")
    assert gs == ["U", "S", "H"]
    print("  GENUINE entry U→S: yes — verifying the SELECTOR atom routes the")
    print("  formula onto the insured branch; soundness is EARNED by the tick")
    print("  that verifies which world you are in.")
    print("  FULL STRICT LADDER U → S → H: realized, rung by rung.")

    print("\n  ✓ E24: the ladder is a temporal logic; hereditary is absorbing;")
    print("    every completed verification path lands on the shelf;")
    print("    and the ladder CAN be climbed rung by rung — sound is earned")
    print("    by verifying which world you are in (the birth-grade")
    print("    conjecture died in §6, same day, in the open).")
