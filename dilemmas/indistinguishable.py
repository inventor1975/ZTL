# -*- coding: utf-8 -*-
"""indistinguishable — two identical quanta: what can be counted, and when probabilities add.

The curator's line of 2026-10-02, after ZQuasi (quasi-sets: the number of ACTS is earned,
the number of OBJECTS is not): "shall we model the physics?" Two measurements, each pinned
below; neither is a new physical prediction, and the file says so.

  I1  THE STATE COUNT. n particles in k cells; what is witnessed is how many clicks each
      cell gave, not which labelled particle sat where. Then "the occupation is (m1..mk)" is
      EARNED, while "the state is this labelled one" — and even "it is one of the labelled
      ones" — stays OPEN. Counting only EARNED distinctions gives C(n+k-1, n), the
      Bose-Einstein count; counting the labelled states, k^n (Maxwell-Boltzmann), counts
      distinctions taken on credit. Measured for (2,2), (3,2), (2,3). NEAR-DEFINITIONAL:
      the physics is put in by the premise "labels are not witnessable" (that IS
      indistinguishability). ZTL adds only the grade: a permuted state is OPEN — neither
      "the same state" (the received quantum view) nor "another state" (the classical one).
      Fermions do not come out (the Pauli exclusion is physics, not logic), nor do
      probabilities (equal weights are a further premise).

  I2  WHEN PROBABILITIES ADD (Hong-Ou-Mandel). Two photons enter a 50:50 beam splitter; a
      coincidence (one click in each output) happens either by both transmitted (tt) or
      both reflected (rr). The classical case split "tt or rr, exclusively" is judged under
      two repertoires:
        - a tag that can tell the photons apart (polarisation, arrival time) is an act over
          tt/rr: the atoms are Z_REDEEMABLE, the split has futures that EARN it — the routes
          are events, and adding their probabilities is licensed: P(coincidence) = 1/2;
        - no such act: tt/rr are Z_PERMANENT, the ceiling is frozen — no future settles the
          split, the routes are not events, there is nothing to add.
      The quantum answer is computed here from amplitudes (overlap of the tags s):
      P(coincidence) = (1 - s)/2 — 1/2 at s = 0, 0 at s = 1 (the HOM dip). ZTL's binary
      stamp matches the two ENDPOINTS: redeemable <-> s = 0 <-> 1/2; permanent <-> s = 1 <->
      the classical sum unlicensed. It does NOT produce the 0 (that is amplitudes), and it
      says nothing about 0 < s < 1 (a partial tag is outside a binary stamp).
      This is Feynman's rule — add probabilities for alternatives distinguishable in
      principle, amplitudes otherwise — and the quantum eraser (remove the tag's act and the
      interference returns) restated: "an event that has a probability" = an atom some act
      in the repertoire can witness. The same refusal as quantum_distributivity.py (forming
      a∧b and a∧b' separately is an act), now on the counting side.

  PRIOR ART, plainly: Feynman's rule; Griffiths' consistent histories (probabilities only
  for histories of a consistent family); Birkhoff-von Neumann quantum logic; Hong, Ou and
  Mandel (1987); for I1 the standard Gibbs/Bose counting. What may be ours is narrow: the
  licensing condition read off one operational judge (zredeem's repertoire) that also
  judges cogito and the kit's letters.

Run:  python3 dilemmas/indistinguishable.py        (asserts every measurement)
"""

import os
import sys
from itertools import product
from math import comb

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

from ztljudge import judge          # noqa: E402
from zredeem import stamp, ceiling  # noqa: E402


def state_count(n, k):
    """-> (labelled states, occupation states, all occupations EARNED, all labelled OPEN)."""
    parts = "ABCDEFGH"[:n]
    occs = {}
    for f in product(range(k), repeat=n):
        occs.setdefault(tuple(f.count(c) for c in range(k)), []).append(f)
    occ_earned = labelled_open = True
    for occ, fs in occs.items():
        o = "O" + "_".join(map(str, occ))
        mark = {o: "T"}
        occ_earned &= judge(o, mark)["disposition"] == "EARNED"
        micro = [" & ".join(f"L{p}{f[i]}" for i, p in enumerate(parts)) for f in fs]
        labelled_open &= judge(f"{o} & ({micro[0]})", mark)["disposition"] == "OPEN"
        anyof = " | ".join(f"({x})" for x in micro)
        labelled_open &= judge(f"{o} & ({anyof})", mark)["disposition"] == "OPEN"
    return k ** n, len(occs), occ_earned, labelled_open


def hom_coincidence(s):
    """Two-photon coincidence probability at a 50:50 beam splitter, tag overlap s in [0,1].
    Amplitudes: transmission 1/sqrt2, reflection i/sqrt2. The two routes to a coincidence
    interfere with weight s (the part of the photons no tag tells apart):
        P = |t t|^2 + |r r|^2 + 2 s Re((t t)(r r)*) = 1/4 + 1/4 + 2 s (-1/4) = (1 - s)/2."""
    t, r = 2 ** -0.5, 1j * 2 ** -0.5
    a, b = t * t, r * r
    return abs(a) ** 2 + abs(b) ** 2 + 2 * s * (a * b.conjugate()).real


def run():
    print("INDISTINGUISHABLE — what can be counted, and when probabilities add")
    print("=" * 72)

    print("\n### I1. The state count")
    for n, k in [(2, 2), (3, 2), (2, 3)]:
        mb, be, occ_ok, lab_ok = state_count(n, k)
        print(f"ok  n={n} k={k}: labelled (on credit) {mb}, EARNED distinct {be}, "
              f"Bose-Einstein C(n+k-1,n) = {comb(n + k - 1, n)}")
        assert be == comb(n + k - 1, n) and mb == k ** n
        assert occ_ok, "every occupation must be EARNED"
        assert lab_ok, "every labelled description must stay OPEN"
    print("ok  occupations EARNED; a labelled state, and 'one of them', OPEN")

    print("\n### I2. When probabilities add (Hong-Ou-Mandel)")
    split = "coinc & ((tt & ~rr) | (rr & ~tt))"
    m = {"coinc": "T", "tt": "Z", "rr": "Z"}
    for label, rep, s in [("a tag tells the photons apart", {"coinc", "tt", "rr"}, 0.0),
                          ("no act tells them apart", {"coinc"}, 1.0)]:
        st = {a: stamp(a, m, rep) for a in ("tt", "rr")}
        c = ceiling(split, m, rep)
        p = hom_coincidence(s)
        print(f"ok  {label:32s} stamps {sorted(set(st.values()))}  frozen={c['ceiling_frozen']}  "
              f"earned futures {c['earned_futures']}/{c['futures']}  QM P(coinc)={p:.3f}")
        if s == 0.0:
            assert set(st.values()) == {"Z_REDEEMABLE_STABLE"} and not c["ceiling_frozen"]
            assert c["earned_futures"] > 0 and abs(p - 0.5) < 1e-12
        else:
            assert set(st.values()) == {"Z_PERMANENT"} and c["ceiling_frozen"]
            assert c["earned_futures"] == 0 and abs(p) < 1e-12
    mid = hom_coincidence(0.5)
    print(f"ok  partial tag s=0.5: QM P(coinc)={mid:.3f} — outside a binary stamp, not claimed")
    assert abs(mid - 0.25) < 1e-12

    print("\nINDISTINGUISHABLE: all measurements hold.")
    print("Counting only what is earned gives the Bose count; the classical count rides credit.")
    print("Probabilities add over atoms some act can witness — Feynman's rule, read off the judge.")


if __name__ == "__main__":
    run()
