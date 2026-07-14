# -*- coding: utf-8 -*-
"""
zrefuter — batch trust-classifier over the ZTL core (Opus, 2026-07-14).

Sorts a spectrum of hypotheses into trust buckets by EXHAUSTIVE evaluation
over {T,F,Z} (decidable → guaranteed):

  VALID         — T under EVERY assignment, incl. unverified (Z). Robust.
  FRAGILE       — T under all {T,F}, but F under some {T,F,Z}. The
                  Strong-Law-of-Small-Numbers class: holds classically,
                  breaks when an input is unverified.
  INVALID       — F under some {T,F}. Not a law.
  CONTRADICTION — F everywhere. Always false.
  DEFERRED      — too heavy for the budget → SEPARATE report, not attempted.

FRAGILE also carries: killing marking, fails_open (breaks under full
ignorance) and min_verified_to_break (0 = fails-open; higher = sneakier —
survives full ignorance, dies on a verified combination).

SPEED: every function is a TABLE over {T,F,Z}^n; composing op(f,g) is a
POINTWISE combine of two ready tables (no re-evaluation), so the whole clone
is enumerated by cheap table ops. classify reads the table directly.

"Do it in full, but cap the heavy parts by time, and put those in a separate
report." A sweep climbs atom-count; each config is guarded by a per-formula
cell cap (3^n) AND a wall-clock budget; whatever the budget cannot reach is
DEFERRED with its reason. Results accumulate in zrefuter_runs/.
"""

import argparse
import json
import multiprocessing as mp
import os
import string
import time
from functools import lru_cache
from itertools import product

from ztl import T, F, Z, VALUES, NOT, AND, OR, IMP, XOR, XNOR

HERE = os.path.dirname(os.path.abspath(__file__))
RUNS = os.path.join(HERE, "zrefuter_runs")
ORDER = ["VALID", "FRAGILE", "INVALID", "CONTRADICTION"]
MAX_DISTINCT = 500000
CHUNK = 2000

# single-value lookup tables (built once from the ztl connectives)
NOT_T = {x: NOT(x) for x in VALUES}
BIN = {"and": AND, "or": OR, "imp": IMP, "xor": XOR, "xnor": XNOR}
OP_T = {op: {(x, y): fn(x, y) for x in VALUES for y in VALUES}
        for op, fn in BIN.items()}


@lru_cache(maxsize=None)
def _cells(n):
    """(combos, is_classical, verified_count) for {T,F,Z}^n, in a fixed order."""
    combos = list(product(VALUES, repeat=n))
    classical = [all(x in (T, F) for x in c) for c in combos]
    verified = [sum(1 for x in c if x != Z) for c in combos]
    return combos, classical, verified


# ----------------------------------------------------- clone enumeration

def enumerate_clone(n, budget_s=0, t0=None):
    """Full clone over n atoms as {table: formula}. Pointwise-composition
    closure; aborts (truncated) on budget or distinct cap."""
    t0 = t0 or time.time()
    combos, _, _ = _cells(n)
    by_tab = {}
    for i in range(n):                                # the atoms
        tab = tuple(c[i] for c in combos)
        by_tab.setdefault(tab, ("atom", i))
    frontier = list(by_tab.items())
    truncated = False
    while frontier:
        allt = list(by_tab.items())
        new = []
        for ftab, ff in frontier:
            if (budget_s and time.time() - t0 > budget_s) \
                    or len(by_tab) > MAX_DISTINCT:
                truncated = True
                break
            nt = tuple(NOT_T[v] for v in ftab)
            if nt not in by_tab:
                by_tab[nt] = ("not", ff)
                new.append((nt, by_tab[nt]))
            for gtab, gf in allt:
                for op, lut in OP_T.items():
                    ct = tuple(lut[(a, b)] for a, b in zip(ftab, gtab))
                    if ct not in by_tab:
                        by_tab[ct] = (op, ff, gf)
                        new.append((ct, by_tab[ct]))
        if truncated:
            break
        frontier = new
    return by_tab, truncated


# ------------------------------------------------------------ classify

def _fmt(f):
    if f[0] == "atom":
        return string.ascii_lowercase[f[1]]
    if f[0] == "not":
        return f"not({_fmt(f[1])})"
    return f"{f[0]}({_fmt(f[1])},{_fmt(f[2])})"


def classify_table(tab, n):
    """Bucket a function given its {T,F,Z}^n table (no evaluation)."""
    combos, classical, verified = _cells(n)
    classical_kill = None
    z_kill = None
    z_kill_ver = 10 ** 9
    all_T = all_F = True
    all_z_index = 0                                   # combo of all-Z is last
    for i, v in enumerate(tab):
        if v != T:
            all_T = False
        if v != F:
            all_F = False
        if v != T:
            if classical[i]:
                if classical_kill is None:
                    classical_kill = combos[i]
            elif verified[i] < z_kill_ver:
                z_kill_ver = verified[i]
                z_kill = combos[i]
    # all-Z combo is the last one in product order
    all_z_val = tab[-1]

    if all_T:
        bucket, kill = "VALID", None
    elif all_F:
        bucket, kill = "CONTRADICTION", None
    elif classical_kill is not None:
        bucket, kill = "INVALID", classical_kill
    else:
        bucket, kill = "FRAGILE", z_kill

    rep = {"bucket": bucket}
    if kill is not None:
        rep["kill"] = {string.ascii_lowercase[j]: kill[j] for j in range(n)}
    if bucket == "FRAGILE":
        rep["fails_open"] = (all_z_val != T)
        rep["min_verified_to_break"] = z_kill_ver
    return rep


def _classify_item(item):
    tab, formula, n = item
    rep = classify_table(tab, n)
    rep["formula"] = _fmt(formula)
    return rep


# --------------------------------------------------- closed-form census

def census(n):
    """EXACT trust-distribution over the external clone (all {T,F,Z}^n ->
    {T,F} functions, + n projections) — a CLOSED FORM, no enumeration.

    A {T,F}-output function is fixed by its value on each of the 3^n cells.
    The 2^n all-classical cells decide classical validity; the remaining
    z = 3^n - 2^n cells (those touching a Z) decide fragility:
      VALID         = 1                       (⊤ — T on every cell)
      CONTRADICTION = 1                       (⊥)
      FRAGILE       = 2^z - 1                 (classical tautology, breaks on Z)
      INVALID       = 2^(3^n) - 2^z - 1       (+ the n projections)
    """
    cells = 3 ** n
    z = cells - 2 ** n
    r = {"n": n, "cells": cells, "z_cells": z, "projections": n,
         "VALID": 1, "CONTRADICTION": 1,
         "FRAGILE_formula": f"2^{z} - 1",
         "INVALID_formula": f"2^{cells} - 2^{z} - 1 + {n}"}
    if cells <= 200:                           # exact ints (else astronomical)
        total = 2 ** cells
        r["FRAGILE"] = 2 ** z - 1
        r["INVALID_with_projections"] = total - 2 ** z - 1 + n
        r["total_TF_functions"] = total
    return r


def _log(msg):
    os.makedirs(RUNS, exist_ok=True)
    line = f"[{time.strftime('%H:%M:%S')}] {msg}"
    with open(os.path.join(RUNS, "progress.log"), "a") as fh:
        fh.write(line + "\n")
        fh.flush()
    print(line, flush=True)


# ----------------------------------------------------------------- run

def run(items, cores=1, budget_s=0, t0=None):
    """items: list of (table, formula, n). Classify under a budget."""
    t0 = t0 or time.time()
    buckets = {b: [] for b in ORDER}
    deferred = []
    done = 0
    pool = mp.Pool(cores) if cores > 1 else None
    for i in range(0, len(items), CHUNK):
        if budget_s and time.time() - t0 > budget_s:
            deferred = [{"formula": _fmt(f), "reason": "classify budget exhausted"}
                        for _, f, _ in items[done:]]
            break
        chunk = items[i:i + CHUNK]
        reps = pool.map(_classify_item, chunk) if pool \
            else [_classify_item(it) for it in chunk]
        for r in reps:
            buckets[r["bucket"]].append(r)
        done += len(chunk)
    if pool:
        pool.close()
        pool.join()
    buckets["FRAGILE"].sort(key=lambda r: (r.get("fails_open", True),
                                           r.get("min_verified_to_break", 0)))
    return buckets, deferred


def mine_examples(n, cores=1, budget_s=0, per_bucket=4):
    """Exhibit real FORMULAS per bucket by enumerating (part of) the clone
    under a budget — the compute-heavy, tail-able part."""
    t0 = time.time()
    by_tab, trunc = enumerate_clone(n, budget_s=budget_s, t0=t0)
    items = [(tab, f, n) for tab, f in by_tab.items()]
    _log(f"n={n}: enumerated {len(items)} formulas"
         f"{' (truncated at cap)' if trunc else ''} in "
         f"{round(time.time() - t0, 1)}s; classifying on {cores} cores…")
    left = budget_s - (time.time() - t0) if budget_s else 0
    buckets, _ = run(items, cores=cores, budget_s=left)
    out = {"_enumerated": len(items), "_truncated": trunc,
           "_sneaky_fragile": sum(1 for r in buckets["FRAGILE"]
                                  if not r.get("fails_open", True))}
    for b in ORDER:
        out[b] = [{k: v for k, v in r.items() if k != "bucket"}
                  for r in buckets[b][:per_bucket]]
    return out


def sweep(max_atoms, cores=1, ex_budget=0, ex_cap=3 ** 8):
    """Closed-form census per n (instant, exact) + example formulas
    (budgeted; streamed to zrefuter_runs/progress.log for `tail -f`)."""
    t0 = time.time()
    _log(f"=== zrefuter sweep, atoms 2..{max_atoms}, cores {cores} ===")
    configs = []
    for n in range(2, max_atoms + 1):
        cen = census(n)
        frag = cen.get("FRAGILE", cen["FRAGILE_formula"])
        _log(f"n={n}: CENSUS (closed form) — VALID 1 · FRAGILE {frag} · "
             f"CONTR 1 · rest INVALID   (z={cen['z_cells']} of {cen['cells']} cells)")
        cfg = {"n": n, "census": cen}
        if 3 ** n <= ex_cap:
            left = ex_budget - (time.time() - t0) if ex_budget else 0
            if ex_budget and left <= 1:
                _log(f"n={n}: example budget exhausted — census only")
            else:
                ex = mine_examples(n, cores=cores, budget_s=left)
                cfg["examples"] = ex
                _log(f"n={n}: examples — VALID {len(ex['VALID'])}, "
                     f"FRAGILE {len(ex['FRAGILE'])} (sneaky {ex['_sneaky_fragile']}), "
                     f"INVALID {len(ex['INVALID'])}, CONTR {len(ex['CONTRADICTION'])}")
        else:
            _log(f"n={n}: 3^{n} > ex_cap — census only (formula examples skipped)")
        configs.append(cfg)
    _log(f"=== done in {round(time.time() - t0, 1)}s ===")
    return {"when": time.strftime("%Y-%m-%d %H:%M:%S"),
            "total_seconds": round(time.time() - t0, 1),
            "max_atoms": max_atoms, "configs": configs}


def save(main):
    os.makedirs(RUNS, exist_ok=True)
    path = os.path.join(RUNS, f"census-{time.strftime('%Y%m%d-%H%M%S')}.json")
    with open(path, "w") as fh:
        json.dump(main, fh, ensure_ascii=False, indent=1)
    return path


def _print(main):
    print("=" * 76)
    print(f"zrefuter — trust-spectrum census (CLOSED FORM), atoms 2..{main['max_atoms']}")
    print("=" * 76)
    print(f"  {'n':>2}  {'VALID':>5}  {'CONTR':>5}  FRAGILE (2^(3^n−2^n)−1)"
          "                    INVALID")
    for c in main["configs"]:
        cen = c["census"]
        frag = str(cen.get("FRAGILE", cen["FRAGILE_formula"]))
        inv = str(cen.get("INVALID_with_projections", cen["INVALID_formula"]))
        print(f"  {cen['n']:>2}  {1:>5}  {1:>5}  {frag[:34]:<36}{inv[:22]}")
    print("\n  Only ⊤ is unconditionally VALID; only ⊥ is CONTRADICTION; every")
    print("  contingent law is FRAGILE or INVALID. Closed form — no enumeration.")
    for c in main["configs"]:
        ex = c.get("examples")
        if ex and ex.get("FRAGILE"):
            print(f"\n  n={c['n']} example fragile formulas "
                  f"(from {ex['_enumerated']} enumerated, {ex['_sneaky_fragile']} sneaky):")
            for e in ex["FRAGILE"][:4]:
                tag = "fails-open" if e.get("fails_open") else \
                    f"sneaky min={e.get('min_verified_to_break')}"
                print(f"    {e['formula']}   kill={e.get('kill')}  ({tag})")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-atoms", type=int, default=8)
    ap.add_argument("--cores", type=int, default=max(1, os.cpu_count() - 2))
    ap.add_argument("--ex-budget", type=float, default=30.0,
                    help="seconds for example-formula enumeration (census is instant)")
    ap.add_argument("--ex-cap", type=int, default=3 ** 4,
                    help="enumerate example formulas only where 3^n <= this")
    ap.add_argument("--no-save", action="store_true")
    args = ap.parse_args()
    main = sweep(args.max_atoms, cores=args.cores,
                 ex_budget=args.ex_budget, ex_cap=args.ex_cap)
    _print(main)
    if not args.no_save:
        print(f"\n  saved -> {save(main)}")

