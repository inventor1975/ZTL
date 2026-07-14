# -*- coding: utf-8 -*-
"""
zhunt — the ZTL warranty hunter. Save the CATCH, count the rest.

Two clean parts, as agreed:

  * HUNTER *gives*: it enumerates candidates — real formulas (bounded node
    count, over N atoms) crossed with every marking {T, F, mark}. Decides
    nothing.
  * The CORE *judges*, exactly like the studio: ztl.ev + the warranty grade
    (zverify.py). For each candidate: a value (T/F/Z-atom) and a grade.

Buckets (by warranty grade, then by direction of the break):

  SAVED — the catch, written line-by-line with WHY (the killing refinement):
    suspect     — SOUND but not hereditary: honest in every completion, yet a
                  hidden break exists (the fallen-lemma class).
    dangerous   — UNTIL-VERIFICATION with value T: a T you cannot trust — it
                  asserts now and verification REVOKES it (the Frege cell).

  COUNTED — the boring mass, statistics only (never written; too big):
    clean       — HEREDITARY: never revoked. "всё ровно."
    deny        — UNTIL-VERIFICATION with value F: a refusal now that
                  verification would GRANT. Safe pessimism.
    atom_z      — a bare marked atom, value Z: the unverified datum itself.

Node-count enumeration is streamed layer by layer so the formula list is never
fully materialised (5 atoms / big node budgets stay in memory bounds). The
originals in the parent dir are imported, never modified.
"""

import argparse
import json
import os
import sys
import time
from itertools import product
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
PARENT = os.path.dirname(HERE)
sys.path.insert(0, PARENT)                       # import the untouched core

from ztl import T, F, Z, show, atoms as f_atoms, OPS2   # noqa: E402
from zmodal import ztl_eval                              # noqa: E402
from zverify import stable_bit, hereditary_bit, refinements  # noqa: E402

BINOPS = list(OPS2.keys())          # and, or, imp, xor, xnor
RESULTS = os.path.join(HERE, "results")
SHARDS = os.path.join(RESULTS, "shards")
# Only `suspect` is written to disk — SOUND but not hereditary = a genuine
# CLASSICAL law (tautology when T) that breaks only under ZTL uncertainty; this
# is the unique-to-ZTL catch. `dangerous` (T-until-verification) is NOT sound,
# so it has a classical countermodel — classical logic already refutes it — so
# it is only COUNTED, never dumped. depth histograms are kept for both.
SAVED = ("suspect",)                       # written to disk (the whole bucket)
TRACKED = ("suspect", "dangerous")         # depth histograms, for statistics
ALL_BUCKETS = ("clean", "suspect", "dangerous", "deny", "atom_z")
SAVE_MIN_DEPTH = 1      # suspect is small and precious — save all of it. Set in run().


# ----------------------------------------------------------------- the HUNTER
def _layers(atom_names, max_nodes):
    """Yield formulas one node-size layer at a time, keeping the DP table of
    smaller formulas (needed to compose larger ones) but never a single flat
    list of everything. Memory ≈ the count of formulas < max_nodes."""
    by_size = {1: list(atom_names)}
    yield list(atom_names)
    for size in range(2, max_nodes + 1):
        cur = [("not", x) for x in by_size.get(size - 1, [])]
        for sx in range(1, size - 1):
            xs, ys = by_size.get(sx, []), by_size.get(size - 1 - sx, [])
            for op in BINOPS:
                for x in xs:
                    for y in ys:
                        cur.append((op, x, y))
        by_size[size] = cur
        yield cur


def chunk_stream(atom_names, max_nodes, chunk):
    """The candidate stream: (chunk_id, [formulas]) lazily, for Pool.imap."""
    cid, buf = 0, []
    for layer in _layers(atom_names, max_nodes):
        for phi in layer:
            buf.append(phi)
            if len(buf) >= chunk:
                yield cid, buf
                cid, buf = cid + 1, []
    if buf:
        yield cid, buf


# ----------------------------------------------------------------- the JUDGE
def _markings(names):
    for combo in product((T, F, "M"), repeat=len(names)):
        yield dict(zip(names, combo))


def _shallowest_kill(phi, marking, v):
    """The reason a non-hereditary verdict breaks: the refinement with the
    fewest verified marks that flips the verdict — the 'вот почему'."""
    best, best_n = None, 10 ** 9
    for m2 in refinements(marking):
        if m2 == marking:
            continue
        if ztl_eval(phi, m2) != v:
            n = sum(1 for a in marking if marking[a] == "M" and m2[a] != "M")
            if n < best_n:
                best, best_n = m2, n
    if best is None:
        return None, None
    kill = {a: best[a] for a in marking if marking[a] == "M" and best[a] != "M"}
    return kill, best_n


def judge(phi, marking):
    """(value, grade, kill, depth) for one candidate — the core's verdict."""
    v = ztl_eval(phi, marking)
    if hereditary_bit(phi, marking):
        return v, "hereditary", None, None
    kill, depth = _shallowest_kill(phi, marking, v)
    grade = "sound" if stable_bit(phi, marking) else "until-verification"
    return v, grade, kill, depth


def bucket_of(v, grade):
    if grade == "hereditary":
        return "clean"
    if grade == "sound":
        return "suspect"
    if v == T:
        return "dangerous"
    if v == F:
        return "deny"
    return "atom_z"                 # v == Z: a bare marked atom


# ------------------------------------------------------------- parallel worker
def _process(args):
    """One chunk → shard files for the SAVED buckets only; full counts and
    depth histograms returned for statistics."""
    cid, formulas = args
    # one shard file per WORKER (append), not per chunk — so the run leaves
    # ~#cores temp files, not one per chunk (which would be tens of thousands).
    handles = {b: open(os.path.join(SHARDS, f"{b}.{os.getpid()}.jsonl"), "a")
               for b in SAVED}
    counts = {b: 0 for b in ALL_BUCKETS}
    written = {b: 0 for b in SAVED}
    depth_hist = {b: {} for b in TRACKED}    # full distribution, for statistics
    pairs = 0
    for phi in formulas:
        names = sorted(f_atoms(phi))
        if not names:
            continue
        s = None
        for marking in _markings(names):
            pairs += 1
            v, grade, kill, depth = judge(phi, marking)
            b = bucket_of(v, grade)
            counts[b] += 1
            if b in TRACKED:
                dh = depth_hist[b]
                dh[depth] = dh.get(depth, 0) + 1
            if b in SAVED and depth is not None and depth >= SAVE_MIN_DEPTH:
                if s is None:
                    s = show(phi)
                rec = {"f": s, "m": {a: marking[a] for a in names},
                       "v": v, "g": grade, "kill": kill, "depth": depth}
                handles[b].write(json.dumps(rec, ensure_ascii=False) + "\n")
                written[b] += 1
    for h in handles.values():
        h.close()
    return cid, counts, written, depth_hist, pairs


def run(atom_names, max_nodes, cores, chunk, save_min_depth):
    global SAVE_MIN_DEPTH
    SAVE_MIN_DEPTH = save_min_depth          # inherited by forked workers
    os.makedirs(SHARDS, exist_ok=True)
    for f in os.listdir(SHARDS):
        os.remove(os.path.join(SHARDS, f))
    log = open(os.path.join(RESULTS, "progress.log"), "w")

    def note(msg):
        line = f"[{time.strftime('%H:%M:%S')}] {msg}"
        print(line); log.write(line + "\n"); log.flush()

    t0 = time.time()
    note(f"HUNTER streaming formulas ≤{max_nodes} nodes over "
         f"{len(atom_names)} atoms {atom_names}; SAVING {SAVED} at depth "
         f"≥{save_min_depth}, counting the rest, on {cores} cores …")

    total = {b: 0 for b in ALL_BUCKETS}
    wtotal = {b: 0 for b in SAVED}
    hist = {b: {} for b in TRACKED}
    pairs = done = 0
    with Pool(cores) as pool:
        for cid, counts, written, dh, p in pool.imap_unordered(
                _process, chunk_stream(atom_names, max_nodes, chunk)):
            for b in ALL_BUCKETS:
                total[b] += counts[b]
            for b in SAVED:
                wtotal[b] += written[b]
            for b in TRACKED:
                for d, n in dh[b].items():
                    hist[b][d] = hist[b].get(d, 0) + n
            pairs += p
            done += 1
            el = time.time() - t0
            note(f"chunk {done}  pairs {pairs:,}  "
                 f"SUSPECT {total['suspect']:,} (SAVED {wtotal['suspect']:,})"
                 f"  | dangerous {total['dangerous']:,} clean {total['clean']:,}"
                 f" deny {total['deny']:,}  ({pairs / el if el else 0:,.0f}/s)")

    note("merging catch shards into one file and cleaning up …")
    for b in SAVED:
        with open(os.path.join(RESULTS, f"{b}.jsonl"), "w") as out:
            for name in sorted(os.listdir(SHARDS)):
                if name.startswith(f"{b}.") and name.endswith(".jsonl"):
                    p = os.path.join(SHARDS, name)
                    with open(p) as f:
                        out.writelines(f)
                    os.remove(p)                  # tidy each shard once merged
    try:
        os.rmdir(SHARDS)                          # drop the now-empty shards dir
    except OSError:
        pass
    summary = {"atoms": atom_names, "max_nodes": max_nodes, "pairs": pairs,
               "save_min_depth": save_min_depth,
               "bucket_totals": total,
               "saved_to_disk": wtotal,
               "depth_hist": {b: {str(k): v for k, v in sorted(
                   hist[b].items(), key=lambda x: (x[0] is None, x[0]))}
                   for b in TRACKED},
               "seconds": round(time.time() - t0, 1)}
    with open(os.path.join(RESULTS, "summary.json"), "w") as f:
        json.dump(summary, f, ensure_ascii=False, indent=2)
    note(f"DONE. pairs {pairs:,}  bucket_totals {total}  "
         f"saved_to_disk {wtotal}  in {summary['seconds']}s")
    log.close()
    return summary


# ------------------------------------------------------------------ regression
def regression():
    """Pin the judge to zverify's MEASURED facts."""
    trophy = ("imp", ("xnor", "d", ("not", "c")),
              ("imp", ("imp", "b", "a"), ("xnor", "b", "c")))
    v, g, kill, depth = judge(trophy, {"a": F, "b": "M", "c": "M", "d": "M"})
    assert v == T and g != "hereditary" and kill == {"b": F, "d": F} \
        and depth == 2, (v, g, kill, depth)
    assert bucket_of(v, g) == "dangerous", g          # T-until-verification
    soundcell = ("or", ("not", ("not", "p")), ("or", "q", ("not", "q")))
    sv, sg, sk, _ = judge(soundcell, {"p": "M", "q": "M"})
    assert sv == T and sg == "sound" and sk == {"p": F}, (sv, sg, sk)
    assert bucket_of(sv, sg) == "suspect"
    iv, ig, _, _ = judge(("imp", "p", "p"), {"p": "M"})   # p→p refusal
    assert iv == F and bucket_of(iv, ig) == "deny", (iv, ig)
    az, ag, _, _ = judge("a", {"a": "M"})                 # bare atom
    assert az == Z and bucket_of(az, ag) == "atom_z", (az, ag)
    print("regression OK: trophy→dangerous(kill b=F,d=F d2); "
          "¬¬p∨(q∨¬q)→suspect(sound,kill p=F); p→p→deny; atom→atom_z(Z)")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--atoms", default="a,b,c,d,e")
    ap.add_argument("--max-nodes", type=int, default=9)
    ap.add_argument("--cores", type=int, default=max(1, os.cpu_count() - 2))
    ap.add_argument("--chunk", type=int, default=2000)
    ap.add_argument("--save-min-depth", type=int, default=1)
    ap.add_argument("--regression", action="store_true")
    a = ap.parse_args()
    if a.regression:
        regression()
    else:
        regression()
        run(a.atoms.split(","), a.max_nodes, a.cores, a.chunk, a.save_min_depth)
