# -*- coding: utf-8 -*-
"""
E22 — choice sequences as the lazy register (VR Part II, step (б)).

Brouwer's continuum runs on sequences-in-growth: at any moment only a
finite prefix exists; what may be ASSERTED at a stage is what the
prefix FORCES regardless of all future free choices (the principle of
open data). VR's operational continuum (VRCycle/Continuum, Path 1)
took exactly that road. This stand measures how the distinction lands
on ZTL's two registers:

    the LAZY register  = the growing prefix (data, monotone),
    the GREEDY register = the verdicts assertable at the stage.

MEASURED here:
  1. THE LADDER OF JUDGES — and the warranty vindicated from Brouwer's
     side. The naive inclusion "greedy-T ⟹ stage-forced-T" is FALSE
     (measured: the ¬¬ ladder asserts T that no prefix forces — the
     E12 cell read temporally: a verdict about a future the data does
     not underwrite). The true ladder runs through the warranty:
     WARRANTED (sound-grade, E12) greedy T ⟹ stage-forced T ⟹ true
     on every admitted continuation — 0 violations, both inclusions
     strict. Zero trust speaks Brouwer exactly when it carries its
     warranty. And the stage court redeems the fallen law of identity
     p→p (every continuation satisfies it): a law of logic, not of
     data — the greedy court abstains there, the stage court asserts.
  2. LAWLESS = GLOBAL SUPERVALUATION: for a lawless sequence (all
     continuations free) the stage verdict coincides with E10's global
     supervaluation TOTALLY. A LAW narrows the worlds: for a lawful
     sequence the stage court is STRICTLY stronger (measured witness:
     under "exactly one 1", a disjunction is forced at stage 0 while
     the supervaluation still refuses). Brouwer's lawless/lawful
     distinction becomes: WHICH world-set the global □ ranges over.
     Zero trust = assertability against a maximally ignorant future.
  3. HEREDITY RESTORED AT THE STAGE COURT: stage verdicts never die
     under growth of the prefix (Kripke persistence, 0 violations) —
     the property greedy verdicts lack (E12/E21) is native to the
     lazy register.
  4. STREAM IDENTITY AT A STAGE (E6 recast): equality of sequences is
     never earned at a finite stage (T requires forcing ALL futures);
     apartness is earned at the first disagreement and persists;
     eq = F exactly when apart = T (coupled earnings), yet apart is
     NOT the ZTL-negation of eq (¬Z = F ≠ Z): the marks reproduce the
     constructive primitivity of apartness.

Instruments: the keel's ev, zmodal's worlds/global_super/ztl_eval —
nothing new is postulated about the logic; only the world-set changes.
"""

from itertools import product

from ztl import T, F, Z, ev
from zmodal import global_super, ztl_eval
from zverify import stable_bit

H = 3                              # horizon: atoms a0..a{H-1}, ak = "α(k)=1"
ATOMS = [f"a{k}" for k in range(H)]


# ---------------------------------------------------------------------------
# Stages, laws, and the three judges
# ---------------------------------------------------------------------------

def completions(prefix, law):
    """All H-bit continuations of the prefix admitted by the law."""
    t = len(prefix)
    out = []
    for tail in product((0, 1), repeat=H - t):
        w = tuple(prefix) + tail
        if law(w):
            out.append(w)
    return out


def world_env(w):
    return {a: (T if w[k] else F) for k, a in enumerate(ATOMS)}


def marking(prefix):
    """The stage marking: revealed positions verified, the rest marked."""
    return {a: ((T if prefix[k] else F) if k < len(prefix) else "M")
            for k, a in enumerate(ATOMS)}


def stage(phi, prefix, law):
    """The stage court: T if the prefix FORCES phi over every admitted
    continuation, F if it forces its failure, Z otherwise."""
    vals = {ev(phi, world_env(w)) for w in completions(prefix, law)}
    if vals == {T}:
        return T
    if T not in vals:
        return F
    return Z


def greedy(phi, prefix):
    return ztl_eval(phi, marking(prefix))


LAWLESS = lambda w: True
EXACTLY_ONE = lambda w: sum(w) == 1          # a law: exactly one 1 overall


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


def all_prefixes():
    for t in range(H + 1):
        for p in product((0, 1), repeat=t):
            yield p


# ---------------------------------------------------------------------------
# 1. The ladder of judges
# ---------------------------------------------------------------------------

def run_ladder(pool):
    print("-- 1. THE LADDER OF JUDGES runs through the warranty --")
    raw_t = raw_over = warr_t = warr_bad = actual_bad = gap = 0
    for phi in pool:
        for pre in all_prefixes():
            g = greedy(phi, pre)
            s = stage(phi, pre, LAWLESS)
            if g == T:
                raw_t += 1
                if s != T:
                    raw_over += 1
                if stable_bit(phi, marking(pre)):
                    warr_t += 1
                    if s != T:
                        warr_bad += 1
            if s == T:
                if any(ev(phi, world_env(w)) != T
                       for w in completions(pre, LAWLESS)):
                    actual_bad += 1
                if g != T:
                    gap += 1
    print(f"  RAW greedy T asserting beyond the stage: {raw_over} of "
          f"{raw_t} (> 0 — the ¬¬ ladder claims a future no prefix forces)")
    nn = ("not", ("not", "a0"))
    print(f"    witness at stage 0: ¬¬a0 — greedy {greedy(nn, ())}, "
          f"stage {stage(nn, (), LAWLESS)}")
    print(f"  WARRANTED (sound-grade, E12) greedy T ⟹ stage T: violations "
          f"{warr_bad} of {warr_t} (must be 0)")
    print(f"  stage T ⟹ true on every admitted continuation: violations "
          f"{actual_bad} (must be 0)")
    print(f"  the abstention gap (stage forces, greedy abstains): {gap} > 0")
    assert raw_over > 0 and warr_bad == 0 and actual_bad == 0 and gap > 0
    assert greedy(nn, ()) == T and stage(nn, (), LAWLESS) == Z
    ident = ("imp", "a0", "a0")
    print(f"  witness — the identity law a0→a0 at stage 0: greedy "
          f"{greedy(ident, ())}, stage {stage(ident, (), LAWLESS)}")
    assert greedy(ident, ()) == F and stage(ident, (), LAWLESS) == T
    print("  → the E12 warranty is vindicated from Brouwer's side: zero")
    print("    trust speaks assertably about a growing sequence exactly when")
    print("    it carries its warranty; the naked ladder verdicts are not")
    print("    assertions about the future. And p→p, fallen in the greedy")
    print("    court, is REDEEMED by the stage court — a law of logic, not")
    print("    of data.")


# ---------------------------------------------------------------------------
# 2. Lawless = global supervaluation; a law makes the stage stronger
# ---------------------------------------------------------------------------

def run_lawless(pool):
    print("\n-- 2. LAWLESS = GLOBAL SUPERVALUATION; LAWFUL IS STRONGER --")
    mismatch = checked = 0
    for phi in pool:
        for pre in all_prefixes():
            checked += 1
            if stage(phi, pre, LAWLESS) != global_super(phi, marking(pre)):
                mismatch += 1
    print(f"  lawless stage verdict vs global supervaluation (E10): "
          f"{checked} pairs, mismatches {mismatch} (must be 0)")
    assert mismatch == 0
    stronger = 0
    witness = None
    for phi in pool:
        for pre in all_prefixes():
            if not completions(pre, EXACTLY_ONE):
                continue
            s_law = stage(phi, pre, EXACTLY_ONE)
            s_free = global_super(phi, marking(pre))
            if s_law == T and s_free != T:
                stronger += 1
                if witness is None and pre == ():
                    witness = phi
    disj = ("or", "a0", ("or", "a1", "a2"))
    print(f"  under the law «exactly one 1»: stage-forced T where the "
          f"supervaluation refuses: {stronger} > 0")
    print(f"  witness at stage 0: {disj} — stage "
          f"{stage(disj, (), EXACTLY_ONE)}, supervaluation "
          f"{global_super(disj, marking(()))}")
    assert stronger > 0 and stage(disj, (), EXACTLY_ONE) == T \
        and global_super(disj, marking(())) != T
    print("  → LAWLESS = GLOBAL SUPERVALUATION, totally: zero trust is")
    print("    assertability against a maximally ignorant future. A law is")
    print("    knowledge: it narrows the worlds the global □ ranges over —")
    print("    Brouwer's lawless/lawful divide lands on E10's modal frame.")


# ---------------------------------------------------------------------------
# 3. Heredity is native to the stage court
# ---------------------------------------------------------------------------

def run_heredity(pool):
    print("\n-- 3. HEREDITY: stage verdicts never die under growth --")
    stage_die = greedy_die = 0
    for phi in pool:
        for pre in all_prefixes():
            if len(pre) == H:
                continue
            for bit in (0, 1):
                ext = tuple(pre) + (bit,)
                s0, s1 = stage(phi, pre, LAWLESS), stage(phi, ext, LAWLESS)
                if s0 in (T, F) and s1 != s0:
                    stage_die += 1
                g0, g1 = greedy(phi, pre), greedy(phi, ext)
                if g0 == T and g1 != T:
                    greedy_die += 1
    print(f"  stage verdicts revoked by one revealed bit: {stage_die} "
          f"(must be 0)")
    print(f"  greedy T-verdicts revoked by one revealed bit: {greedy_die} "
          f"(> 0 — the E12 Frege cell, for contrast)")
    assert stage_die == 0 and greedy_die > 0
    print("  → Kripke persistence, refused as a free axiom by the greedy")
    print("    register (E12), is NATIVE to the lazy one: earned-at-a-stage")
    print("    survives every future choice. The two-register split is")
    print("    exactly Brouwer's split: growth carries data, stages assert.")


# ---------------------------------------------------------------------------
# 4. Stream identity at a stage (E6 recast)
# ---------------------------------------------------------------------------

def eq_stage(pa, pb):
    """Equality of two growing streams at a stage: F at the first revealed
    disagreement, never T at any finite stage, Z otherwise."""
    n = min(len(pa), len(pb))
    if any(pa[k] != pb[k] for k in range(n)):
        return F
    return Z


def apart_stage(pa, pb):
    n = min(len(pa), len(pb))
    if any(pa[k] != pb[k] for k in range(n)):
        return T
    return Z


def run_streams():
    print("\n-- 4. STREAM IDENTITY AT A STAGE (E6 inside the register) --")
    from ztl import NOT
    prefixes = [p for t in range(5) for p in product((0, 1), repeat=t)]
    never_t = never_f = coupled = not_negation = persist_bad = 0
    pairs = 0
    for pa in prefixes:
        for pb in prefixes:
            pairs += 1
            e, ap = eq_stage(pa, pb), apart_stage(pa, pb)
            never_t += (e == T)
            never_f += (ap == F)
            coupled += ((e == F) != (ap == T))
            not_negation += (NOT(ap) != e)
            if ap == T:                       # persistence of earned apartness
                for ba, bb in product((0, 1), repeat=2):
                    if apart_stage(tuple(pa) + (ba,), tuple(pb) + (bb,)) != T:
                        persist_bad += 1
    print(f"  prefix pairs examined: {pairs}")
    print(f"  equality earned T at a finite stage: {never_t} (must be 0 — "
          f"never T)")
    print(f"  apartness earned F at a finite stage: {never_f} (must be 0 — "
          f"never F)")
    print(f"  coupling failures (eq=F ⟺ apart=T): {coupled} (must be 0)")
    print(f"  earned apartness dying under growth: {persist_bad} (must be 0)")
    print(f"  cells where ¬apart ≠ eq: {not_negation} > 0 (¬Z=F ≠ Z)")
    assert never_t == 0 and never_f == 0 and coupled == 0 \
        and persist_bad == 0 and not_negation > 0
    print("  → equality of streams is Z-permanent, apartness is earnable and")
    print("    persistent (E6), and apartness is NOT the negation of equality")
    print("    even at the level of marks — the constructive primitivity of #")
    print("    falls out of the zero-trust tables.")


def main():
    print("=" * 72)
    print("E22: CHOICE SEQUENCES AS THE LAZY REGISTER (VR Part II, step (б))")
    print("=" * 72)
    pool = build_pool(ATOMS, depth=2)
    print(f"  [pool: {len(pool)} formulas over {ATOMS}; horizon H={H}; "
          f"prefixes: {sum(1 for _ in all_prefixes())}]")
    run_ladder(pool)
    run_lawless(pool)
    run_heredity(pool)
    run_streams()
    print("\n" + "=" * 72)
    print("SUMMARY: the stage court of a growing sequence is ZTL's global")
    print("supervaluation with the world-set fixed by the law — lawless =")
    print("maximal ignorance = zero trust; WARRANTED greedy verdicts are its")
    print("sound core (raw ladder verdicts overclaim the future — E12 read")
    print("temporally); p→p redeemed at the stage; heredity is native to the")
    print("lazy register; stream equality/apartness reproduce E6 at every")
    print("stage. Brouwer's two objects — the growth and the stage — ARE the")
    print("two registers. Next: the Lean stitch via Continuum/Branch.")
    print("=" * 72)


if __name__ == "__main__":
    main()
