# -*- coding: utf-8 -*-
"""
E21 — operational sets under ZTL verdicts (VR Part II, step (а)).

The VR set theory's native register, VR-SetsOp, carries identity as a
WITNESSED BISIMULATION: x ≈ y holds when a bisimulation relation between
the two pointed reveal-graphs is produced and carried along — no
quotient, no choice. This stand models finite operational sets as
pointed graphs and measures how their identity atoms behave as ZTL
atoms: witness → earned T, separation → earned F (apartness at a finite
stage, as in E6), unexamined → Z, verdicts and warranties on top.

MEASURED here:
  1. The earner: on a finite zoo every identity atom decides — T with a
     checkable witness or F with a finite separation stage. Identity on
     finite operational sets is TOTALLY EARNABLE (the Z is an input
     mark, not a fate — contrast E6, where stream equality is
     Z-permanent).
  2. Deduplication is earned: {∅,∅} ≈ {∅} with an explicit witness —
     closing E5's story ({Z,Z} ≠ {Z}: merging unverified members is NOT
     earned; merging WITNESSED-identical members IS).
  3. Alive ZTL rules over ≈-atoms are backed by witness CONSTRUCTORS:
     refl = diagonal, symm = converse, trans = composition,
     ∪-congruence = union — every constructed witness re-checked.
  4. Verdicts before verification — AND A FIND THAT REACHES BACK INTO
     E12. Raw greedy T-verdicts over Z-atoms can be FALSE of the facts
     (the ¬¬ cell on identity atoms). The supervaluation warranty of
     E12 restores SOUNDNESS (warranted T is never false of the facts,
     0 violations) — but NOT persistence: this stand's larger pool
     found supervaluation-stable T-verdicts that die under truthful
     verification. Canonical cell: ¬¬p ∨ (q∨¬q) — a T held up by a
     ladder (greedy ¬¬Z=T) and insured by a gap (q∨¬q true in all
     completions but greedy-F); verifying p:=F kicks the ladder before
     the gap closes. Cross-checked against zverify.py's own functions:
     stable_bit=True, invariant_under_all_verifications=False. So
     E12's equivalence theorem (stability ⟺ invariance) and its
     monotonicity claim are POOL-RELATIVE, not general: the 10-formula
     E12 pool lacks the or(ladder, gap) shape. What survives: the
     soundness half of the warranty. The true fence for shelf life is
     HEREDITARY invariance (verdict unchanged under every partial
     refinement), measured here: 0 deaths, totally. Enacted 2026-07-12:
     the two-grade warranty ladder is canon (zverify.py revised,
     preprint §19 → v1.1, unpublished).
  5. Cardinality of a collection with unverified identity = an interval
     (E5/E8); truthful verification narrows it monotonically, and
     partition consistency (= witness composition) can earn the last
     atom for free.
  6. lfp/gfp orthogonality: a CYCLIC SENTENCE (liar) is a permanent
     refusal (greedy jump oscillates, period 2 — quarantine, lfp
     leftover), while a CYCLIC SET (Ω = {Ω}) earns identity at once
     (bisimulation is gfp-shaped): Ω ≈ Ω₂ measured T, IsGrounded(Ω)
     measured False. Groundedness of the SET and earnability of its
     IDENTITY are orthogonal — the set-side mirror of AFA-as-theorem.
"""

from itertools import product

from ztl import T, F, Z, ev, NOT

# ---------------------------------------------------------------------------
# Finite operational sets: pointed reveal-graphs  (succ: tuple of tuples)
# ---------------------------------------------------------------------------

def empty():
    return ((tuple(),), 0)                      # one node, no reveals


def sup(members):
    """The set OF the given operational sets (disjoint-union builder)."""
    succ = [None]
    roots = []
    for msucc, mpt in members:
        base = len(succ)
        for ch in msucc:
            succ.append(tuple(c + base for c in ch))
        roots.append(mpt + base)
    succ[0] = tuple(roots)
    return (tuple(succ), 0)


def vn(k):
    """Von Neumann natural k = {0, …, k-1}."""
    return sup([vn(i) for i in range(k)]) if k else empty()


OMEGA = ((tuple([0]),), 0)                       # Ω = {Ω}: one node, self-loop
OMEGA2 = (((1,), (0,)), 0)                       # two-node cycle a={b}, b={a}
DUP = (((1, 2), tuple(), tuple()), 0)            # {∅,∅}: two reveal-edges to ∅


# ---------------------------------------------------------------------------
# The earner: greatest bisimulation with separation stages
# ---------------------------------------------------------------------------

def bisim(x, y):
    """Maximal bisimulation between the node sets; stage[(a,b)] = the
    finite stage at which the pair separated (apartness earned)."""
    sx, _ = x
    sy, _ = y
    R = {(a, b) for a in range(len(sx)) for b in range(len(sy))}
    stage = {}
    t = 0
    changed = True
    while changed:
        t += 1
        changed = False
        for a, b in sorted(R):
            ok = (all(any((a2, b2) in R for b2 in sy[b]) for a2 in sx[a])
                  and all(any((a2, b2) in R for a2 in sx[a]) for b2 in sy[b]))
            if not ok:
                R.discard((a, b))
                stage[(a, b)] = t
                changed = True
    return R, stage


def check_witness(x, y, R):
    """The cheap side of the asymmetry: verify a CARRIED witness."""
    sx, px = x
    sy, py = y
    if (px, py) not in R:
        return False
    return all(all(any((a2, b2) in R for b2 in sy[b]) for a2 in sx[a])
               and all(any((a2, b2) in R for a2 in sx[a]) for b2 in sy[b])
               for a, b in R)


def eq_earn(x, y):
    """Run the earner: ('T', witness) or ('F', separation stage)."""
    R, stage = bisim(x, y)
    px, py = x[1], y[1]
    if (px, py) in R:
        return T, R
    return F, stage[(px, py)]


def is_grounded(x):
    """IsGrounded = no cycle reachable from the point (well-founded reveals)."""
    succ, pt = x
    seen = set()

    def dfs(a, path):
        if a in path:
            return False
        if a in seen:
            return True
        seen.add(a)
        return all(dfs(c, path | {a}) for c in succ[a])

    return dfs(pt, frozenset())


# ---------------------------------------------------------------------------
# 1 + 2. The zoo: total earnability; dedup earned
# ---------------------------------------------------------------------------

ZOO = [
    ("∅", empty()),
    ("{∅}", sup([empty()])),
    ("{{∅}}", sup([sup([empty()])])),
    ("vn2 = {∅,{∅}}", vn(2)),
    ("vn3", vn(3)),
    ("{∅,∅} (dup)", DUP),
    ("Ω = {Ω}", OMEGA),
    ("Ω₂ (2-cycle)", OMEGA2),
]


def run_zoo():
    print("-- 1. THE ZOO: every identity atom decides (witness or stage) --")
    undecided = bad_witness = 0
    t_pairs = []
    for i, (nx, x) in enumerate(ZOO):
        for ny, y in ZOO[i:]:
            v, cert = eq_earn(x, y)
            if v == T:
                ok = check_witness(x, y, cert)
                bad_witness += (not ok)
                t_pairs.append((nx, ny))
                print(f"  T  {nx} ≈ {ny}   [witness |R|={len(cert)}, re-checked "
                      f"{'✓' if ok else 'FAIL'}]")
            elif v == F:
                print(f"  F  {nx} ≉ {ny}   [apartness earned at stage {cert}]")
            else:
                undecided += 1
    assert undecided == 0 and bad_witness == 0
    print(f"  Undecided: {undecided}; bad witnesses: {bad_witness}.")
    print("  → IDENTITY IS TOTALLY EARNABLE on finite operational sets")
    print("    (contrast E6: stream equality is Z-permanent — finiteness is")
    print("    what buys totality, not the logic).")

    print("\n-- 2. DEDUPLICATION IS EARNED --")
    v, w = eq_earn(DUP, sup([empty()]))
    assert v == T and check_witness(DUP, sup([empty()]), w)
    print(f"  {{∅,∅}} ≈ {{∅}}: T with witness |R|={len(w)} — dedup EARNED.")
    print("  E5 measured {Z,Z} ≠ {Z}: merging UNVERIFIED members is not")
    print("  earned. Together: deduplication happens exactly when identity")
    print("  is witnessed — the two-register story closes.")
    return t_pairs


# ---------------------------------------------------------------------------
# 3. Witness constructors = the alive rules
# ---------------------------------------------------------------------------

def run_constructors():
    print("\n-- 3. WITNESS CONSTRUCTORS BACK THE ALIVE RULES --")
    checks = 0
    for _, x in ZOO:                                     # refl = diagonal
        d = {(a, a) for a in range(len(x[0]))}
        assert check_witness(x, x, d)
        checks += 1
    tw = {}
    for i, (nx, x) in enumerate(ZOO):
        for j, (ny, y) in enumerate(ZOO):
            v, c = eq_earn(x, y)
            if v == T:
                tw[(i, j)] = c
    for (i, j), R in tw.items():                         # symm = converse
        conv = {(b, a) for a, b in R}
        assert check_witness(ZOO[j][1], ZOO[i][1], conv)
        checks += 1
    for (i, j), R in tw.items():                         # trans = composition
        for (j2, k), S in tw.items():
            if j2 == j:
                comp = {(a, c) for a, b in R for b2, c in S if b == b2}
                assert check_witness(ZOO[i][1], ZOO[k][1], comp)
                checks += 1
    for (i, j), R in tw.items():                         # sup-congruence
        if i != j:
            X, Y = sup([ZOO[i][1]]), sup([ZOO[j][1]])
            lifted = {(a + 1, b + 1) for a, b in R} | {(0, 0)}
            assert check_witness(X, Y, lifted)
            checks += 1
    print(f"  refl=diagonal, symm=converse, trans=composition, {{·}}-congruence")
    print(f"  = union+root: {checks} constructed witnesses, ALL re-checked ✓.")
    print("  → The ZTL rules alive on ≈-atoms are not table luck: each is")
    print("    backed by a witness constructor (Lean: Equiv.refl/symm/trans,")
    print("    zero axioms — the port target for SetsZTL).")


# ---------------------------------------------------------------------------
# 4. Verdicts before verification: raw greedy vs warranted (Э12)
# ---------------------------------------------------------------------------

def build_pool(names, depth=2):
    layers = [list(names)]
    for _ in range(depth):
        prev = [f for layer in layers for f in layer]
        new = [("not", a) for a in layers[-1]]
        for op in ("and", "or", "imp"):
            for a in layers[-1]:
                for b in prev:
                    new.append((op, a, b))
            for a in prev:
                for b in layers[-1]:
                    if (op, a, b) not in new:
                        new.append((op, a, b))
        layers.append(new)
    return [f for layer in layers for f in layer]


def run_verdicts():
    print("\n-- 4. VERDICTS OVER Z-ATOMS: raw / supervaluation / hereditary --")
    # facts about x={∅}, y={∅,∅}, z=vn2:  a: x≈y (T), b: x≈z (F), c: y≈z (F)
    facts = {"a": eq_earn(sup([empty()]), DUP)[0],
             "b": eq_earn(sup([empty()]), vn(2))[0],
             "c": eq_earn(DUP, vn(2))[0]}
    assert facts == {"a": T, "b": F, "c": F}
    names = sorted(facts)
    pool = build_pool(names, depth=2)
    # partial valuations: each atom is either verified (to its fact) or Z
    valuations = [dict(zip(names, combo))
                  for combo in product(*[(facts[n], Z) for n in names])]

    def refinements(v, values):
        """All assignments of the given classical values to any subset
        of the still-Z atoms (v itself included)."""
        free = [n for n in names if v[n] == Z]
        for combo in product((Z,) + values, repeat=len(free)):
            yield {**v, **dict(zip(free, combo))}

    def stable(phi, v):
        """E12's supervaluation warranty: every FULL completion agrees
        with the current greedy verdict."""
        w = ev(phi, v)
        return all(ev(phi, c) == w
                   for c in refinements(v, (T, F))
                   if all(c[n] != Z for n in names))

    def hereditary(phi, v):
        """The candidate true fence: the verdict is unchanged under
        EVERY partial refinement (arbitrary classical values)."""
        w = ev(phi, v)
        return all(ev(phi, r) == w for r in refinements(v, (T, F)))

    raw_t = raw_false = sv_t = sv_false = her_t = 0
    for phi in pool:
        truth = ev(phi, facts)
        for v in valuations:
            if ev(phi, v) == T:
                raw_t += 1
                raw_false += (truth != T)
                if stable(phi, v):
                    sv_t += 1
                    sv_false += (truth != T)
                    her_t += hereditary(phi, v)
    print(f"  Formula pool over 3 ≈-atoms: {len(pool)}; partial valuations: "
          f"{len(valuations)} (verified-to-fact or Z per atom).")
    print(f"  SOUNDNESS. Raw greedy T-verdicts: {raw_t}, FALSE of the facts: "
          f"{raw_false} (>0:")
    print("    the ¬¬ ladder reports T about an identity that is factually F).")
    print(f"  Supervaluation-warranted (Э12) T: {sv_t}, false of the facts: "
          f"{sv_false} (must be 0)")
    assert raw_false > 0 and sv_false == 0
    print("  → the SOUNDNESS half of the Э12 warranty holds: warranted T is")
    print("    never a lie about operational identity. SOUND about the facts: 0.")

    # persistence under truthful verification (v' verifies more atoms)
    raw_die = sv_die = her_die = 0
    dying_example = None
    for phi in pool:
        for v in valuations:
            if ev(phi, v) != T:
                continue
            for v2 in valuations:
                if v2 != v and all(v[n] in (Z, v2[n]) for n in names) \
                        and ev(phi, v2) != T:
                    raw_die += 1
                    if stable(phi, v):
                        sv_die += 1
                        if dying_example is None:
                            dying_example = (phi, dict(v), dict(v2))
                    if hereditary(phi, v):
                        her_die += 1
    print(f"\n  PERSISTENCE. T-verdicts dying under truthful verification:")
    print(f"    raw {raw_die} (>0 — expected, E12's Frege cell);")
    print(f"    supervaluation-warranted {sv_die} — THE FIND: > 0!")
    print(f"    hereditary-warranted {her_die} (must be 0)")
    assert raw_die > 0 and sv_die > 0 and her_die == 0
    phi, v, v2 = dying_example
    print(f"    dying warranted cell: {phi}")
    print(f"      at {v} → verdict T, supervaluation-stable")
    print(f"      after truthful {v2} → verdict {ev(phi, v2)}")
    print("  Canonical shape or(ladder, gap): ¬¬p ∨ (q∨¬q) — greedy T via the")
    print("  ladder, insured by a gap that is true in ALL completions yet")
    print("  greedy-F; verification kicks the ladder before the gap closes.")
    print("  Cross-checked with zverify.py's own stable_bit/invariance: the")
    print("  E12 equivalence theorem and monotonicity are POOL-RELATIVE —")
    print("  they falsify on this larger pool. THE FENCE IS HEREDITARY:")
    print(f"  invariance under every partial refinement ({her_t} of {sv_t} "
          f"warranted T-verdicts are hereditary).")
    print("  → verdict = (value, warranty) stands, but the warranty splits:")
    print("    supervaluation buys soundness; only hereditary invariance buys")
    print("    shelf life. Curator's decision 2026-07-12: the warranty is a")
    print("    two-grade ladder — canon in zverify.py; preprint §19 revised")
    print("    for v1.1 (unpublished until the ship is checked further).")


# ---------------------------------------------------------------------------
# 5. Cardinality intervals narrow under verification
# ---------------------------------------------------------------------------

def run_cardinality():
    print("\n-- 5. CARDINALITY = INTERVAL; verification narrows it --")
    # collection [x, y, z] with the same facts: x≈y, x≉z, y≉z → true size 2
    PARTS = [[[0, 1, 2]], [[0, 1], [2]], [[0, 2], [1]], [[1, 2], [0]],
             [[0], [1], [2]]]
    atoms_ = {("x", "y"): T, ("x", "z"): F, ("y", "z"): F}
    idx = {"x": 0, "y": 1, "z": 2}

    def interval(verified):
        sizes = []
        for part in PARTS:
            blk = {e: i for i, b in enumerate(part) for e in b}
            if all((blk[idx[a]] == blk[idx[b]]) == (val == T)
                   for (a, b), val in verified.items()):
                sizes.append(len(part))
        return min(sizes), max(sizes)

    chain = [{}]
    for k in [("x", "y"), ("x", "z"), ("y", "z")]:
        chain.append({**chain[-1], k: atoms_[k]})
    prev = None
    for verified in chain:
        lo, hi = interval(verified)
        tag = ""
        if prev is not None:
            assert prev[0] <= lo and hi <= prev[1]
            tag = " ⊆ previous ✓"
        if len(verified) == 2 and (lo, hi) == (2, 2):
            tag += "  ← the last atom earned FREE by partition consistency"
        print(f"  verified {len(verified)}/3 atoms: |{{x,y,z}}| ∈ [{lo},{hi}]{tag}")
        prev = (lo, hi)
    assert prev == (2, 2)
    print("  → narrowing is monotone (0 violations), endpoint = the truth;")
    print("    consistency = witness composition working for free (cf. §3).")


# ---------------------------------------------------------------------------
# 6. lfp/gfp: cyclic sentence vs cyclic set
# ---------------------------------------------------------------------------

def run_orthogonality():
    print("\n-- 6. CYCLES: SENTENCE vs SET (lfp vs gfp) --")
    trace = [Z]
    for _ in range(4):
        trace.append(NOT(trace[-1]))
    assert trace[1] != trace[2] and trace[1:3] == trace[3:5]   # period 2
    print(f"  Liar L := ¬Tr(L), greedy jump from Z: {' → '.join(trace)}")
    print("  — oscillation period 2, no fixed point: PERMANENT refusal")
    print("    (quarantine, the lfp leftover — fixedpoint.py, zpassport.py).")
    v, w = eq_earn(OMEGA, OMEGA2)
    assert v == T and check_witness(OMEGA, OMEGA2, w)
    print(f"  Set Ω = {{Ω}} vs the 2-cycle Ω₂: ≈ earned T (witness |R|={len(w)},")
    print(f"    re-checked ✓), while IsGrounded(Ω) = {is_grounded(OMEGA)} and "
          f"IsGrounded(vn2) = {is_grounded(vn(2))}.")
    assert not is_grounded(OMEGA) and is_grounded(vn(2))
    print("  → ORTHOGONALITY: groundedness of the SET is independent of the")
    print("    earnability of its IDENTITY. Identity is gfp-shaped (survives")
    print("    refutation from above), sentence-grounding is lfp-shaped")
    print("    (earned from below): the same cycle that dooms a sentence is")
    print("    harmless in a set — AFA-as-theorem is the set-side mirror of")
    print("    quarantine-as-theorem. Two registers, one architecture.")


def main():
    print("=" * 72)
    print("E21: OPERATIONAL SETS UNDER ZTL VERDICTS (VR Part II, step (а))")
    print("=" * 72)
    run_zoo()
    run_constructors()
    run_verdicts()
    run_cardinality()
    run_orthogonality()
    print("\n" + "=" * 72)
    print("SUMMARY: witnessed identity IS a ZTL atom discipline — T earned by")
    print("a checkable bisimulation, F earned at a finite separation stage,")
    print("Z until examined; alive rules = witness constructors; cardinality")
    print("narrows monotonically; set-cycles earn what sentence-cycles never")
    print("do. AND: the E12 warranty splits in two — supervaluation buys")
    print("soundness, only hereditary invariance buys shelf life (the")
    print("equivalence theorem was pool-relative). Enacted: the two-grade")
    print("ladder is canon (zverify.py revised, preprint §19 → v1.1).")
    print("Next: Lean SetsZTL in VRCycle.")
    print("=" * 72)


if __name__ == "__main__":
    main()
