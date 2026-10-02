# -*- coding: utf-8 -*-
"""many_worlds — Everett's branches through the ZTL lens: what can be counted, located and believed.

Third modern target (the curator's line of 2026-10-02). The prediction was written BEFORE this file ran
(ztl-private/notes/MWI-PREDICTION-2026-10-02.md, 12:15).

  THE SETUP. A measurement of a|up> + b|down> in Everett's reading: both outcomes occur, in two branches,
  each with its own observer and record. Open: where the Born weights |a|^2, |b|^2 come from (counting
  branches gives 1/2 each); "which branch am I in"; and whether "the other branches are real" says anything.

  M1  THE NUMBER OF BRANCHES IS NOT AN OBSERVABLE (physics, asserted). Let the down-branch decohere into k
      orthogonal environment records. Branch counting then gives P(up) = 1/(k+1) — it changes with k —
      while the Born weight |a|^2 does not. No act inside a branch witnesses the count; in ZTL "there are
      n branches" is Z_PERMANENT, and so is every probability built by counting them. ZTL refuses the
      branch-counting rule (Wallace's side) — and does NOT produce |a|^2: that is amplitudes again.

  M2  SELF-LOCATION IS AN UNREDEEMED ATOM. After branching, before looking, "I am in the up-branch" is
      Z_REDEEMABLE (my own record will settle it); after looking, EARNED. Vaidman's self-locating
      uncertainty, in ZTL terms, is ordinary credit with a known act of repayment.

  M3  THE OTHER BRANCH IS PERMANENT CREDIT. "Another branch exists in which I saw down" is Z_PERMANENT for
      any observer in a branch — and so is its denial. No earned claim separates one world from many: the
      ceiling of "the other branch exists" is frozen, and so is the ceiling of "it does not". The same
      conservativity schema as Plato's Forms, Hume's ought and Descartes' owner (ZTL lean/*_Conservativity):
      what every metaphysics buys, it buys with a bridge no act can cross.

  PRIOR ART, plainly: Everett (1957); Deutsch (1999) and Wallace (2012) — decision-theoretic Born rule, the
  branch count not well defined; Vaidman, Sebens & Carroll — self-locating uncertainty; the standard
  "empirical equivalence of interpretations" objection. Not new physics. What is ours: the three answers
  fall out of the same judge and the same stamp as the rest of the series (indistinguishable, bell,
  wigner_friends, firewall).

Run:  python3 dilemmas/many_worlds.py        (asserts every measurement)
"""

import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

from ztljudge import judge          # noqa: E402
from zredeem import ceiling, stamp  # noqa: E402

BORN_UP = Fraction(1, 3)            # |a|^2


def branch_weights(k):
    """Down-branch split into k equal environment records. -> (Born P(up), counting P(up), total weight)."""
    weights = [BORN_UP] + [(1 - BORN_UP) / k] * k
    return weights[0], Fraction(1, k + 1), sum(weights)


def run():
    print("MANY WORLDS — what can be counted, located and believed")
    print("=" * 72)

    print("\n### M1. The number of branches is not an observable")
    for k in (1, 2, 5, 10):
        born, count, total = branch_weights(k)
        print(f"ok  down-branch split into {k:2d}: Born P(up) = {born}, branch counting P(up) = {count}, total {total}")
        assert born == BORN_UP and total == 1 and count == Fraction(1, k + 1)
    m = {"n_branches": "Z", "rec_up": "Z"}
    st = stamp("n_branches", m, {"rec_up"})          # an observer's acts reach her own record only
    c = ceiling("n_branches", m, {"rec_up"})
    print(f"ok  'there are n branches': {st}, ceiling frozen = {c['ceiling_frozen']}")
    assert st == "Z_PERMANENT" and c["ceiling_frozen"]

    print("\n### M2. Self-location is an unredeemed atom")
    before = stamp("rec_up", m, {"rec_up"})
    after = judge("rec_up", {"rec_up": "T"})["disposition"]
    print(f"ok  'I am in the up-branch' before looking: {before}; after looking: {after}")
    assert before == "Z_REDEEMABLE_STABLE" and after == "EARNED"

    print("\n### M3. The other branch is permanent credit")
    m3 = {"rec_up": "T", "other_down": "Z"}
    rep = {"rec_up"}
    yes = ceiling("other_down", m3, rep)
    no = ceiling("~other_down", m3, rep)
    st3 = stamp("other_down", m3, rep)
    print(f"ok  'another branch exists where I saw down': {st3}; frozen = {yes['ceiling_frozen']}; "
          f"its denial frozen = {no['ceiling_frozen']}")
    assert st3 == "Z_PERMANENT" and yes["ceiling_frozen"] and no["ceiling_frozen"]

    print("\nMANY WORLDS: all measurements hold.")
    print("Branches cannot be counted, self-location is ordinary credit, and one world vs many is a bridge no act crosses.")


if __name__ == "__main__":
    run()
