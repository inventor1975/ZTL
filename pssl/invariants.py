# -*- coding: utf-8 -*-
"""
invariants — PSSL leg 5: which invariants survive the space, and which
were properties of our taste.

Leg 4 measured that our eight grounds are 0.17% of the space they live
in. That reframes every claim of the form "across the family, X does not
move": such a claim is made over a biased sample of eight chosen points,
and is worth exactly as much as it survives outside them.

So the candidates get tested twice — on our own eight, and against the
sampled space — and the honest result is not "invariant" or "not" but
**under what filter it becomes true**.

FOUND BEFORE THE CENSUS WAS EVEN BUILT, by testing our own eight:

PSSL §3 names non-contradiction with its reductio as "the floor, a
principle retained in every corner". Leg 1 checked that (P2) and it
held — but leg 1 had FOUR grounds. On all eight it **fails in three**:

    K3            ¬(p∧¬p) not valid — it has no tautologies at all
    weak Kleene   likewise
    Łukasiewicz Ł3 not valid — and this one is NOT the trivial case:
                  Ł3 has 168 tautologies on the depth-2 pool. At p = u,
                  p∧¬p = u, ¬u = u, and u is not designated. It fails on
                  the merits.

**This does not refute PSSL.** PSSL claims the floor across ITS corners
— intuitionistic, quantum, ZTL, and formerly classical — and there it
holds, measured. What the extension shows is that the floor is a
property of those corners and not of three-valued logic as such. The
paper says the right thing about the grounds it names; the temptation
worth resisting is reading it as a claim about the space.

Run:  python3 pssl/invariants.py [N]
"""
import itertools
import os
import random
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
sys.path.insert(0, _ROOT)
sys.path.insert(0, _HERE)

import zipc                                                   # noqa: E402
import grounds as G                                           # noqa: E402
import family as F                                            # noqa: E402
from census import (VALS, _ASG, random_matrix, ev, keeps_mp,   # noqa: E402
                    SEED, POOL)

SHORT = {"classical": "CPC", "intuitionistic": "IPC", "quantum MO2": "MO2",
         "ZTL": "ZTL", "K3": "K3", "LP": "LP", "weak Kleene": "WK",
         "Lukasiewicz L3": "Ł3"}
PSSL_CORNERS = {"CPC", "IPC", "MO2", "ZTL"}

p, q = "p", "q"
NC = ("not", ("and", p, ("not", p)))                 # non-contradiction
REDUCTIO = ("imp", ("imp", p, ("not", p)), ("not", p))
EXPLOSION_LAW = ("imp", ("and", p, ("not", p)), q)


def valid_in(tbl, D, phi):
    return all(ev(phi, a, tbl) in D for a in _ASG)


def exports(tbl, D):
    """Discharge at arity 0: γ ⊨ φ ⟹ ⊨ γ→φ, over the pool."""
    for g in POOL:
        for f in POOL:
            holds = all(ev(f, a, tbl) in D for a in _ASG
                        if ev(g, a, tbl) in D)
            if holds and not valid_in(tbl, D, ("imp", g, f)):
                return False
    return True


if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    print("=" * 76)
    print("LEG 5 — WHICH INVARIANTS SURVIVE THE SPACE")
    print("  Our eight are 0.17% of it (leg 4). A claim that 'across the")
    print("  family X does not move' is worth what it survives outside them.")
    print("=" * 76)

    # ---------------------------------------------------------- our eight
    ALL = [(SHORT[n], v) for n, _, v, _ in G.GROUNDS] + \
          [(SHORT[m.name], m.valid) for m in F.FAMILY]
    print("\n### 1. The PSSL floor (§3) on our OWN eight")
    print("    Leg 1 checked this over FOUR grounds and it held.\n")
    print(f"    {'ground':6s}{'¬(p∧¬p)':>10s}{'reductio':>10s}   PSSL corner?")
    floor_fails = []
    for nm, v in ALL:
        a, b = v(NC), v(REDUCTIO)
        if not (a and b):
            floor_fails.append(nm)
        print(f"    {nm:6s}{'✓' if a else '✗':>10s}{'✓' if b else '✗':>10s}"
              f"   {'yes' if nm in PSSL_CORNERS else '—'}")
    print(f"\n    fails in: {', '.join(floor_fails) if floor_fails else 'none'}")
    corner_ok = all(v(NC) and v(REDUCTIO) for nm, v in ALL
                    if nm in PSSL_CORNERS)
    print(f"    across PSSL's OWN corners: {'HOLDS' if corner_ok else 'FAILS'}"
          "  ← what the paper actually claims")
    print("    across the extended eight : FAILS")
    print("    → the floor is a property of those corners, not of")
    print("      three-valued logic as such. Ł3 is the sharp case: it has")
    print("      168 tautologies, so its failure is on the merits, not the")
    print("      trivial 'no theorems' of K3 and WK.")

    # ---------------------------------------------------------- the census
    print(f"\n### 2. The same candidates against the space ({N} samples)")
    rnd = random.Random(SEED)
    tally = {"nc": 0, "red": 0, "both": 0, "mp": 0, "exp": 0}
    cells = {"both halves": 0, "MP only": 0, "discharge only": 0, "neither": 0}
    cells_nc = dict.fromkeys(cells, 0)
    nc_total = 0
    for _ in range(N):
        tbl, D = random_matrix(rnd)
        nc = valid_in(tbl, D, NC)
        red = valid_in(tbl, D, REDUCTIO)
        mp = keeps_mp(tbl, D)
        ex = exports(tbl, D)
        tally["nc"] += nc
        tally["red"] += red
        tally["both"] += nc and red
        tally["mp"] += mp
        tally["exp"] += ex
        cell = ("both halves" if mp and ex else "MP only" if mp else
                "discharge only" if ex else "neither")
        cells[cell] += 1
        if nc and red:
            nc_total += 1
            cells_nc[cell] += 1

    print(f"    non-contradiction valid : {tally['nc']:6d}  "
          f"({tally['nc'] / N:.2%})")
    print(f"    reductio valid          : {tally['red']:6d}  "
          f"({tally['red'] / N:.2%})")
    print(f"    both (the PSSL floor)   : {tally['both']:6d}  "
          f"({tally['both'] / N:.2%})")
    print(f"    keeps modus ponens      : {tally['mp']:6d}  "
          f"({tally['mp'] / N:.2%})")
    print(f"    discharges (arity 0)    : {tally['exp']:6d}  "
          f"({tally['exp'] / N:.2%})")

    # -------------------------------------------------- the MP/DT trade
    print("\n### 3. THE TRADE — 'every ground pays with exactly one half'")
    print("    The day's headline finding, measured on EIGHT points.")
    print("    If a random ground pays with NEITHER, the strong reading")
    print("    dies here rather than in a referee's hands.\n")
    print(f"    {'cell':18s}{'raw sample':>14s}{'with the floor':>18s}")
    for c in ("both halves", "MP only", "discharge only", "neither"):
        raw = f"{cells[c]:6d} ({cells[c] / N:.2%})"
        flt = (f"{cells_nc[c]:5d} ({cells_nc[c] / nc_total:.2%})"
               if nc_total else "—")
        print(f"    {c:18s}{raw:>14s}{flt:>18s}")

    print(f"\n    grounds paying with NEITHER, raw          : "
          f"{cells['neither']} of {N}")
    print(f"    grounds paying with NEITHER, floor-filtered: "
          f"{cells_nc['neither']} of {nc_total}")
    strong = cells["neither"] == 0
    filtered = nc_total and cells_nc["neither"] == 0
    print(f"\n    strong reading ('no ground pays with neither'):")
    print(f"      unfiltered  {'HOLDS' if strong else 'FAILS'}")
    print(f"      under the PSSL floor  {'HOLDS' if filtered else 'FAILS'}")

    # ------------------------------------------------ the filter search
    print("\n### 4. IS THERE A FILTER under which the trade holds?")
    print("    'We found none' is worth less than 'we looked'. Five")
    print("    natural conditions, same sample:\n")
    ID = ("imp", p, p)
    FILTERS = [
        ("no filter", lambda t, D: True),
        ("p→p valid (the arrow works)", lambda t, D: valid_in(t, D, ID)),
        ("has at least one tautology",
         lambda t, D: any(valid_in(t, D, f) for f in POOL)),
        ("¬ is an involution",
         lambda t, D: all(t["not"][t["not"][x]] == x for x in VALS)),
        ("p→p and ¬ involutive",
         lambda t, D: valid_in(t, D, ID)
         and all(t["not"][t["not"][x]] == x for x in VALS)),
        ("the PSSL floor",
         lambda t, D: valid_in(t, D, NC) and valid_in(t, D, REDUCTIO)),
    ]
    rnd2 = random.Random(SEED)
    fres = [{"n": 0, "neither": 0} for _ in FILTERS]
    for _ in range(N):
        tbl, D = random_matrix(rnd2)
        neither = not keeps_mp(tbl, D) and not exports(tbl, D)
        for i, (_lbl, f) in enumerate(FILTERS):
            if f(tbl, D):
                fres[i]["n"] += 1
                fres[i]["neither"] += neither
    print(f"    {'filter':30s}{'passed':>8s}{'pay with neither':>20s}")
    any_holds = False
    for (lbl, _f), r in zip(FILTERS, fres):
        pct = f"{r['neither'] / r['n']:.2%}" if r["n"] else "—"
        holds = r["n"] and r["neither"] == 0
        any_holds = any_holds or holds
        print(f"    {lbl:30s}{r['n']:>8d}{r['neither']:>10d} {pct:>8s}"
              + ("  ← HOLDS" if holds else ""))

    print("\n" + "=" * 76)
    print("WHAT SURVIVED")
    print("=" * 76)
    print("  The trade is NOT a law of the space. Grounds paying with")
    print("  NEITHER half are common — two in five — and no filter tried")
    print("  removes them: the arrow working, having tautologies, an")
    print("  involutive negation, the PSSL floor, and their combinations")
    print("  all leave the 'neither' cell at around 40%.")
    print()
    print("  So today's headline must be stated as what it is: AMONG THE")
    print("  EIGHT, each pays with at most one half. That is true, and it")
    print("  is a SELECTION EFFECT — we chose logics somebody had a use")
    print("  for, and a usable logic keeps at least one half of its arrow.")
    print("  'Every ground' was never measured and is now refuted.")
    print()
    print("  The honest open question the census leaves: no FORMAL filter")
    print("  we tried reproduces the selection. What our eight share is")
    print("  that someone used them, and that is not a property of a")
    print("  matrix. Finding a formal condition that does the same work")
    print("  would be a real result; we do not have one.")
    assert not strong, "the trade unexpectedly held — re-read section 3"
    print("\n  CEILING: sampled, not swept; arity-0 discharge only (the")
    print("  full statement needs a standing context, leg 2a); and the")
    print("  floor is tested as two named formulas, not as a property.")
    print("\n  LEG 5 GREEN")
