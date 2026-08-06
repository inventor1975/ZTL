# -*- coding: utf-8 -*-
"""
Expedition E27: redeemability — which credit can ever be repaid.

THE WORD-SPEC (agreed 2026-08-06, the Plato thread; settled BEFORE code).

E24 time is the arrival of ground: one tick = verify(atom: Z → T/F), and
E24 silently assumes every atom HAS such an act available. E27 removes the
assumption. Acts form an explicit REPERTOIRE — a set of atoms over which a
verifying act is defined at all. What the repertoire does not cover, no
sequence of acts will ever touch.

  REDEEMABLE  (reach)  an atom p is redeemable from marking m under
              repertoire R iff some finite admissible sequence of acts
              ends with mark(p) ≠ Z.  Admissible = each act verifies an
              atom that is still Z at its turn.  ∃-sequence, not ∃-act:
              single-act redemption is the degenerate case.
  Z-PERMANENT the negation, proved by INVARIANT: a property preserved by
              every act in R on which mark(p)=Z holds.  Base case, and the
              Plato case: p ∉ dom(R) — no act is defined over p at all, so
              "mark(p) stays Z" survives every tick trivially.
  HOLD        (E25's amendment) reaching non-Z is not keeping it: where
              ground expires, redemption must also be HELD.  Here reach is
              implemented fully; hold enters only as the stamp split below
              — full E25 integration is future work, stated honestly.

  THE PASSPORT BRIDGE (E18).  E18 classifies a refusal by its INTERNAL
  anatomy (dependency SCCs: PARADOX / INTRINSIC / UNDERDETERMINED / INPUT /
  DOWNSTREAM).  E27 classifies it by the EXTERNAL repertoire — an
  orthogonal axis.  Three new stamps for a Z-atom:

      Z_PERMANENT            no act in the repertoire is defined over it;
      Z_REDEEMABLE_DECAYING  an act exists but its ground expires (E25);
      Z_REDEEMABLE_STABLE    an act exists and its ground is monotone (E24).

  E18's PARADOX is Z-permanent under EVERY repertoire (no consistent act
  exists even in principle) — the internal axis dominates there.

  CEILINGS.  For a formula, the judge's weak links split by stamp, and the
  reachable GRADE CEILING follows: resolve every redeemable link over all
  its futures, keep every Z-permanent link at Z, and take the best grade
  any future attains.  A package whose weak links are all redeemable can
  in principle be EARNED; one carrying a Z-permanent link has its ceiling
  frozen at credit — no possible future settles it.

  WHY THIS FLOOR EXISTS (the measured finale).  First-order content cannot
  separate Aristotle's exit from the operational one: every operational
  model extends conservatively to a grounded one (machine-checked,
  lean/Plato_Conservativity.lean — absence has no formula).  Redeemability
  separates them: THE SAME FORMULA SHAPE under two repertoires gets two
  different ceilings.  Aristotle's ∃g carries no act — his package rides
  permanent credit; the operational package's links are application
  records, each with an act — its credit is repayable in finitely many
  ticks.  Redeemability is NOT invariant under the translation that FO
  cannot see through; it is a warrant-invariant, not a model-invariant.
  That is the differentiator's whole content — and the honest caveat with
  it: ranking packages by redeemability is a STIPULATION (the criterion is
  itself operational — a fixed point, not a verdict), recorded here before
  any opponent records it for us.

MEASURED (this file, deterministic, re-run to reproduce): see __main__ —
  * BFS over act sequences CONFIRMS the invariant prediction exactly
    (reachable ⟺ in-repertoire), no divergence on the Plato atom set;
  * Plato package (frozen link eg — no act): EARNED futures = 0, and the
    measured asymmetry found on this file's first run: a hereditary future
    still exists — a REFUTED one. Unredeemable credit can die forever; it
    can never be earned. Settlement is one-directional for it;
  * operational package (links a1, b — acts over each): EARNED future
    exists among the four;
  * same shape, swapped repertoires: ceilings swap with them — the
    differentiator lives in the repertoire, not the formula.
"""

from itertools import product

from ztljudge import check

Z = "Z"


# ------------------------------------------------------------ repertoire
def domain(repertoire):
    """The set of atoms some act is defined over."""
    return set(repertoire)


def z_atoms(marking):
    return {a for a, v in marking.items() if v == Z}


# ------------------------------------------------------------ reach (E24)
def redeemable(atom, marking, repertoire):
    """Reach, by honest BFS over admissible act sequences — NOT by the
    shortcut `atom in repertoire`.  The shortcut is the invariant PREDICTION;
    the BFS is its measurement (they must agree, and __main__ checks it)."""
    if marking.get(atom, Z) != Z:
        return True                      # already out of quarantine
    frontier = [frozenset(z_atoms(marking))]
    seen = set(frontier)
    while frontier:
        nxt = []
        for still_z in frontier:
            if atom not in still_z:
                return True
            for a in still_z:
                if a in repertoire:      # an act exists and is admissible
                    child = still_z - {a}
                    if child not in seen:
                        seen.add(child)
                        nxt.append(child)
        frontier = nxt
    return False


def z_permanent(atom, marking, repertoire):
    """The invariant proof, stated as code: no act is defined over `atom`,
    hence 'mark(atom) = Z' is preserved by every admissible act."""
    return marking.get(atom, Z) == Z and atom not in repertoire


# ------------------------------------------------------------ stamps (E18)
def stamp(atom, marking, repertoire, expiring=frozenset()):
    """The E27 passport stamp of one Z-atom under one repertoire."""
    if marking.get(atom, Z) != Z:
        return "GROUNDED"
    if atom not in repertoire:
        return "Z_PERMANENT"
    return "Z_REDEEMABLE_DECAYING" if atom in expiring else "Z_REDEEMABLE_STABLE"


# ------------------------------------------------------------ ceilings
def ceiling(text, marking, repertoire):
    """Best and worst grade over every future the repertoire can produce:
    redeemable links resolve both ways, Z-permanent links stay Z forever."""
    base = check(text, marking)
    weak = base["unverified"]
    frozen = [a for a in weak if a not in repertoire]
    live = [a for a in weak if a in repertoire]
    futures = []
    for combo in product("TF", repeat=len(live)):
        m = dict(base["marking"])
        m.update(dict(zip(live, combo)))
        futures.append(check(text, m))
    if not futures:
        futures = [base]
    earned = [r for r in futures
              if r["grade"] == "hereditary" and r["verdict"] == "T"]
    refuted = [r for r in futures
               if r["grade"] == "hereditary" and r["verdict"] == "F"]
    return {"formula": base["formula"], "weak": weak, "frozen": frozen,
            "live": live, "futures": len(futures),
            "earned_futures": len(earned), "refuted_futures": len(refuted),
            # frozen ceiling = no future EARNS it; being refutable is not
            # a ceiling — death is always available to a bad package
            "ceiling_frozen": bool(frozen) and not earned}


# ------------------------------------------------------------ the measure
def run():
    print("E27. REDEEMABILITY: which credit can ever be repaid")
    print("=" * 66)

    atoms = ["g", "s", "n", "r", "u", "q", "m", "a1", "a2", "b"]
    marking = {a: Z for a in atoms}
    OPERATIONAL = {"a1", "a2", "b"}          # acts exist: count applications
    PLATONIC = set()                          # no act is defined over a Form

    print("\n### 1. BFS measurement vs the invariant prediction")
    diverged = 0
    for repertoire, tag in [(OPERATIONAL, "operational"), (PLATONIC, "empty")]:
        for a in atoms:
            bfs = redeemable(a, marking, repertoire)
            predicted = a in repertoire
            ok = bfs == predicted
            diverged += 0 if ok else 1
        print(f"  repertoire {tag:12s}: BFS == invariant prediction on "
              f"{len(atoms)}/{len(atoms)} atoms")
    assert diverged == 0, "invariant broken — the shortcut lies"

    print("\n### 2. Stamps for the Plato weak links (repertoire: operational)")
    for a in ["s", "n", "u", "a1", "b"]:
        print(f"  {a}: {stamp(a, marking, OPERATIONAL)}")
    assert stamp("s", marking, OPERATIONAL) == "Z_PERMANENT"
    assert stamp("a1", marking, OPERATIONAL) == "Z_REDEEMABLE_STABLE"

    print("\n### 3. Ceilings: same shape, two vocabularies")
    #   the ground warrants the character; ground asserted
    aris = "(eg -> b) & eg"
    oper = "(a1 -> b) & a1"
    m2 = {x: Z for x in ["eg", "b", "a1"]}
    ca = ceiling(aris, m2, {"b"})              # b observable, ∃g has no act
    co = ceiling(oper, m2, {"a1", "b"})        # every link has an act
    for tag, c in [("Aristotle", ca), ("operational", co)]:
        print(f"  {tag:12s} {c['formula']:18s} frozen={c['frozen'] or '—'} "
              f"earned={c['earned_futures']}/{c['futures']} "
              f"refuted={c['refuted_futures']}/{c['futures']}")
    assert ca["ceiling_frozen"] and ca["earned_futures"] == 0
    assert not co["ceiling_frozen"] and co["earned_futures"] >= 1
    # the measured asymmetry, found by the first run of this file: the
    # frozen package still HAS a hereditary future — a REFUTED one (b:=F
    # kills the conjunction regardless of eg). A package on unredeemable
    # links can die forever; it can never be earned. Settlement is
    # available to it in one direction only.
    assert ca["refuted_futures"] >= 1

    print("\n### 4. The differentiator is the repertoire, not the formula")
    swapped = ceiling(oper, m2, {"b"})         # SAME formula, acts withdrawn
    print(f"  operational shape under Plato's repertoire: "
          f"earned={swapped['earned_futures']}/{swapped['futures']}, "
          f"refuted={swapped['refuted_futures']}/{swapped['futures']}")
    assert swapped["ceiling_frozen"]
    print("  -> ceilings follow the repertoire; redeemability is not an")
    print("     interpretation invariant (lean/Plato_Conservativity.lean is")
    print("     why nothing at the formula level could have done this).")

    print("\n### 5. The stipulation, on the record")
    print("  Ranking packages by redeemability favours the operational one")
    print("  BECAUSE the measure of warrant is itself operational: a fixed")
    print("  point, not a verdict. Stated here before any opponent states it.")
    print("\nE27: all assertions hold.")
    return 0


if __name__ == "__main__":
    import sys
    sys.exit(run())
