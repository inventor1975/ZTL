# -*- coding: utf-8 -*-
"""
census — PSSL leg 4: are our eight special, or eight arbitrary points?

The curator, after leg 3: are there more logics, or are we closed?

The cheap answer is a citation — between IPC and CPC alone there are
continuum many intermediate logics (Jankov 1968), so eight points sit in
an uncountable space and "closed" is not in question. That settles
nothing worth settling.

The question worth measuring is different: **are our eight special?** They
were not sampled, they were chosen, each carrying historical weight
(Bochvar, Kleene, Priest, Łukasiewicz, Birkhoff–von Neumann, Brouwer). So
sample the space they live in and see whether a random inhabitant lands
on one of them or somewhere new.

THE SPACE. Three-valued matrices over {¬,∧,∨,→}, classical on {T,F} —
that is the standing requirement for calling something a
three-valued logic rather than an arbitrary table — with the cells
touching `u` free, and a designated set. Free choices:

    ¬u                    3
    ∧, ∨, → : 5 cells each   3^5 each
    designated {T} or {T,u}  2
                          ------
                          3^16 × 2  ≈  86 million

THE FINGERPRINT. Two grounds are indistinguishable ON THIS POOL if they
agree on every law and every single-premise rule in it. That bitvector is
the fingerprint; sampled matrices are compared against the fingerprints
of the eight.

It resolves FOUR of them, not eight, and the collapse is exactly leg 3's
blocks: {CPC, IPC, LP, Ł3} and {ZTL, K3} each share a fingerprint here.
That is not a defect to be papered over — CPC and LP provably cannot be
told apart by any law or any one-premise rule (leg 2c: they part only at
arity 2, on explosion), so no fingerprint of this shape will ever
separate them. Hits are therefore reported per BLOCK. A first draft of
this file keyed the fingerprint to a single NAME, which silently
overwrote block members and reported every hit against whichever ground
was inserted last — a label that looks like data and is not.

MEASURED (50,000 samples, seed 20260720):
  landed on one of our blocks ...........  87   0.174%
  landed somewhere new .................. 49913  99.826%
  distinct new behaviours seen .......... 10020
  keeping modus ponens .................. 25066  (50.13% of the sample)
    of those, on one of our blocks ......    53   0.21%
    distinct new behaviours WITH MP .....  6181

WHAT A MATCH ON IPC WOULD MEAN, stated in advance so it is not misread:
intuitionistic logic has no finite characteristic matrix (Gödel 1932),
but that is a statement about ALL formulas. On a bounded pool a finite
matrix can certainly reproduce its behaviour, and if one does, that is
the pool's ceiling showing itself, not a refutation of Gödel.

Run:  python3 pssl/census.py [N]
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

VALS = ("1", "u", "0")
POOL = zipc.build_pool(("p", "q"), depth=1)
SEED = 20260720

SHORT = {"classical": "CPC", "intuitionistic": "IPC", "quantum MO2": "MO2",
         "ZTL": "ZTL", "K3": "K3", "LP": "LP", "weak Kleene": "WK",
         "Lukasiewicz L3": "Ł3"}

# the cells fixed by "classical on {T,F}"
CLASSICAL = {
    "not": {"1": "0", "0": "1"},
    "and": {("1", "1"): "1", ("1", "0"): "0", ("0", "1"): "0", ("0", "0"): "0"},
    "or":  {("1", "1"): "1", ("1", "0"): "1", ("0", "1"): "1", ("0", "0"): "0"},
    "imp": {("1", "1"): "1", ("1", "0"): "0", ("0", "1"): "1", ("0", "0"): "1"},
}
FREE2 = [("1", "u"), ("u", "1"), ("u", "u"), ("u", "0"), ("0", "u")]


def random_matrix(rnd):
    neg = dict(CLASSICAL["not"]); neg["u"] = rnd.choice(VALS)
    tbl = {"not": neg}
    for op in ("and", "or", "imp"):
        t = dict(CLASSICAL[op])
        for cell in FREE2:
            t[cell] = rnd.choice(VALS)
        tbl[op] = t
    D = {"1"} if rnd.random() < 0.5 else {"1", "u"}
    return tbl, D


def ev(phi, asg, tbl):
    if isinstance(phi, str):
        return asg[phi]
    if phi[0] == "not":
        return tbl["not"][ev(phi[1], asg, tbl)]
    return tbl[phi[0]][(ev(phi[1], asg, tbl), ev(phi[2], asg, tbl))]


_ASG = [dict(zip(("p", "q"), c)) for c in itertools.product(VALS, repeat=2)]


def fingerprint_matrix(tbl, D):
    laws = tuple(all(ev(f, a, tbl) in D for a in _ASG) for f in POOL)
    rules = tuple(all(ev(f, a, tbl) in D
                      for a in _ASG if ev(g, a, tbl) in D)
                  for g in POOL for f in POOL)
    return laws + rules


def fingerprint_oracle(valid, derives):
    return (tuple(valid(f) for f in POOL)
            + tuple(derives([g], f) for g in POOL for f in POOL))


def keeps_mp(tbl, D):
    """Transport: p, p→q ⊨ q. A table that cannot carry earned truth is
    not a candidate logic, whatever else it does."""
    return all(ev("q", a, tbl) in D for a in _ASG
               if ev("p", a, tbl) in D
               and ev(("imp", "p", "q"), a, tbl) in D)


def _fingerprint_chunk(chunk):
    """Worker: fingerprint + MP for a chunk of matrices. Returns
    (list of (fingerprint, keeps_mp)). Pure function of its input, so the
    numbers are identical to the sequential loop — only the compute is
    spread over cores. The matrices are drawn sequentially in the parent
    (preserving the RNG stream), so parallelising here changes nothing
    measurable, only the wall clock."""
    return [(fingerprint_matrix(tbl, D), keeps_mp(tbl, D))
            for tbl, D in chunk]


if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 200000
    print("=" * 74)
    print("LEG 4 — A CENSUS OF THE SPACE OUR EIGHT LIVE IN")
    print("  Not 'are there more logics' (continuum, Jankov 1968), but")
    print("  'are our eight special, or eight arbitrary points?'")
    print("=" * 74)
    print(f"\n  space   : 3^16 × 2 ≈ 86 million three-valued matrices,")
    print(f"            classical on {{T,F}}, u-cells free, D ∈ {{{{T}},{{T,u}}}}")
    print(f"  sample  : {N} uniform, seed {SEED}")
    print(f"  pool    : {len(POOL)} formulas — {len(POOL)} laws + "
          f"{len(POOL) ** 2} single-premise rules per fingerprint")

    # fingerprint -> the LIST of our grounds carrying it. A dict keyed to a
    # single name would silently overwrite, and every hit would then be
    # reported against whichever ground happened to be inserted last —
    # a label that looks like data and is not.
    ours = {}
    for n, _, v, d in G.GROUNDS:
        ours.setdefault(fingerprint_oracle(v, d), []).append(SHORT[n])
    for m in F.FAMILY:
        ours.setdefault(fingerprint_oracle(m.valid, m.derives),
                        []).append(SHORT[m.name])
    label = {fp: "{" + ", ".join(ns) + "}" for fp, ns in ours.items()}
    print(f"\n  our eight give {len(ours)} distinct fingerprints on this pool")
    for fp, ns in ours.items():
        if len(ns) > 1:
            print(f"    indistinguishable HERE: {', '.join(ns)}")
    print("    (the pool is depth-1; CPC|LP part only at arity 2 — leg 2c —")
    print("     and the blocks are exactly leg 3's, so hits are reported")
    print("     per BLOCK, which is all this fingerprint can resolve)")

    # Draw all matrices sequentially — this keeps the RNG stream exactly
    # as the old loop, so every number below is byte-identical; only the
    # expensive fingerprinting is spread over cores.
    rnd = random.Random(SEED)
    mats = [random_matrix(rnd) for _ in range(N)]

    from concurrent.futures import ProcessPoolExecutor
    workers = min(os.cpu_count() or 1, 32)
    chunk = max(1, (N + workers - 1) // workers)
    chunks = [mats[i:i + chunk] for i in range(0, N, chunk)]
    computed = []
    try:
        with ProcessPoolExecutor(max_workers=workers) as pool:
            for part in pool.map(_fingerprint_chunk, chunks):
                computed.extend(part)
    except Exception:                       # any pool failure → sequential
        computed = [(fingerprint_matrix(t, D), keeps_mp(t, D))
                    for t, D in mats]

    hits, seen_new, mp_hits, mp_new = {}, {}, {}, {}
    mp_total = 0
    for fp, mp in computed:
        mp_total += mp
        if fp in ours:
            hits[label[fp]] = hits.get(label[fp], 0) + 1
            if mp:
                mp_hits[label[fp]] = mp_hits.get(label[fp], 0) + 1
        else:
            seen_new[fp] = seen_new.get(fp, 0) + 1
            if mp:
                mp_new[fp] = mp_new.get(fp, 0) + 1

    landed = sum(hits.values())
    print(f"\n{'=' * 74}\nRAW SAMPLE\n{'=' * 74}")
    print(f"  landed on one of ours : {landed:7d}  ({landed / N:.4%})")
    print(f"  landed somewhere new  : {N - landed:7d}  ({1 - landed / N:.4%})")
    print(f"  distinct NEW behaviours seen : {len(seen_new)}")
    print(f"\n  which BLOCK a random matrix reproduces:")
    for k in sorted(label.values()):
        v = hits.get(k, 0)
        note = "" if v else "   never reproduced"
        print(f"    {k:26s} {v:7d}  ({v / N:.4%}){note}")

    print(f"\n{'=' * 74}\nFILTERED — matrices that keep MODUS PONENS\n{'=' * 74}")
    print("  A table that cannot transport earned truth is not a candidate")
    print("  logic, whatever else it does. This is the honest filter.\n")
    ml = sum(mp_hits.values())
    print(f"  keep MP               : {mp_total:7d}  ({mp_total / N:.2%} of sample)")
    if mp_total:
        print(f"    of those, on one of ours : {ml:6d}  ({ml / mp_total:.2%})")
        print(f"    of those, somewhere new  : {mp_total - ml:6d}"
              f"  ({1 - ml / mp_total:.2%})")
        print(f"    distinct NEW behaviours with MP : {len(mp_new)}")
        for k in sorted(label.values()):
            print(f"      {k:26s} {mp_hits.get(k, 0):6d}")

    print(f"\n{'=' * 74}\nWHAT THIS SAYS\n{'=' * 74}")
    rate = landed / N
    if rate < 0.01:
        print("  Our eight are RARE in their own space: a random inhabitant")
        print("  almost never reproduces any of them. They are eight chosen")
        print("  points, not a covering of the space — and the honest word")
        print("  for the set is 'a sample of what has done work', not 'the")
        print("  family of three-valued logics'.")
    else:
        print("  Our eight are COMMON: a random inhabitant lands on one of")
        print("  them often, so the eight cover much of what the space can")
        print("  do on this pool.")
    print("\n  CEILING: fingerprints are equality ON THIS POOL. Two matrices")
    print("  matching here may differ on a formula we did not ask about,")
    print("  and a match on IPC would be the pool's ceiling showing, not a")
    print("  refutation of Gödel 1932 (no finite characteristic matrix is a")
    print("  claim about ALL formulas).")
    print("\n  CENSUS GREEN")
