# -*- coding: utf-8 -*-
"""
zhunt — the ZTL warranty hunter, with the corpus SAVED this time.

Two clean parts, as agreed:

  * HUNTER *gives*: it enumerates candidates — real formulas (bounded size,
    over N atoms) crossed with every marking {T, F, mark}. It decides
    nothing.
  * The CORE *judges*, exactly like the studio: ztl.ev / the warranty grade
    (zverify.py) — for each candidate it returns a value (T/F) and a
    warranty GRADE. Whatever it catches is written to disk.

The overnight hunt of 2026-07-12 (the "151.8M pairs" run) streamed and
asserted, then threw the list away — only counts and one trophy survived.
This run keeps it, sorted into three files by warranty grade:

  results/clean.jsonl       — HEREDITARY: the verdict is never revoked under
                              any verification.  "всё ровно."
  results/suspect.jsonl     — SOUND but NOT hereditary: honest in every
                              completion, yet a hidden break exists — we
                              write WHY (the killing refinement, à la the
                              fallen lemma / §5 trophy).  "ошибка, вот почему."
  results/unverified.jsonl  — UNTIL-VERIFICATION: alive only until the first
                              check, then flips.  "не проверено, на всякий
                              случай."

Every candidate is caught (T, F, with or without marks) — nothing is
dropped. Originals in the parent dir are imported, never modified.
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

from ztl import T, F, ev, show, atoms as f_atoms, OPS2   # noqa: E402
from zmodal import ztl_eval                              # noqa: E402
from zverify import stable_bit, hereditary_bit, refinements  # noqa: E402

BINOPS = list(OPS2.keys())          # and, or, imp, xor, xnor
RESULTS = os.path.join(HERE, "results")
SHARDS = os.path.join(RESULTS, "shards")
BUCKETS = ("clean", "suspect", "unverified")


# ----------------------------------------------------------------- the HUNTER
def gen_formulas(atom_names, max_nodes):
    """Every distinct formula TREE with node-count ≤ max_nodes over the atoms
    (node = one atom or one operator). Deterministic, duplicate-free by
    construction — this is what 'gives' the candidates."""
    by_size = {1: list(atom_names)}
    out = list(atom_names)
    for size in range(2, max_nodes + 1):
        cur = []
        for x in by_size.get(size - 1, []):          # unary  not(x)
            cur.append(("not", x))
        for sx in range(1, size - 1):                # binary op(x,y)
            sy = size - 1 - sx
            xs, ys = by_size.get(sx, []), by_size.get(sy, [])
            for op in BINOPS:
                for x in xs:
                    for y in ys:
                        cur.append((op, x, y))
        by_size[size] = cur
        out.extend(cur)
    return out


# ----------------------------------------------------------------- the JUDGE
def _markings(names):
    """Every marking of the atoms present: each atom T | F | 'M' (mark)."""
    for combo in product((T, F, "M"), repeat=len(names)):
        yield dict(zip(names, combo))


def _shallowest_kill(phi, marking, v):
    """The reason a non-hereditary verdict breaks: the refinement with the
    FEWEST verified marks that flips the verdict. This is the 'вот почему'."""
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
    """The core's verdict on one candidate: (value, grade, kill, depth)."""
    v = ztl_eval(phi, marking)
    if hereditary_bit(phi, marking):
        return v, "hereditary", None, None
    kill, depth = _shallowest_kill(phi, marking, v)
    grade = "sound" if stable_bit(phi, marking) else "until-verification"
    return v, grade, kill, depth


def _bucket(grade):
    return {"hereditary": "clean", "sound": "suspect",
            "until-verification": "unverified"}[grade]


# ------------------------------------------------------------- parallel worker
def _process(args):
    """One chunk of formulas → its own shard files. Returns per-bucket counts
    and pairs processed (so the main loop can stream progress)."""
    cid, formulas = args
    handles = {b: open(os.path.join(SHARDS, f"{b}.{cid}.jsonl"), "w")
               for b in BUCKETS}
    counts = {b: 0 for b in BUCKETS}
    pairs = 0
    for phi in formulas:
        names = sorted(f_atoms(phi))
        if not names:
            continue
        s = show(phi)
        for marking in _markings(names):
            pairs += 1
            v, grade, kill, depth = judge(phi, marking)
            b = _bucket(grade)
            counts[b] += 1
            rec = {"f": s, "m": {a: marking[a] for a in names},
                   "v": v, "g": grade}
            if kill is not None:
                rec["kill"] = kill
                rec["depth"] = depth
            handles[b].write(json.dumps(rec, ensure_ascii=False) + "\n")
    for h in handles.values():
        h.close()
    return cid, counts, pairs


def _chunks(seq, size):
    for i in range(0, len(seq), size):
        yield seq[i:i + size]


def run(atom_names, max_nodes, cores, chunk):
    os.makedirs(SHARDS, exist_ok=True)
    for f in os.listdir(SHARDS):
        os.remove(os.path.join(SHARDS, f))
    log = open(os.path.join(RESULTS, "progress.log"), "w")

    def note(msg):
        line = f"[{time.strftime('%H:%M:%S')}] {msg}"
        print(line); log.write(line + "\n"); log.flush()

    t0 = time.time()
    note(f"HUNTER: enumerating formulas ≤{max_nodes} nodes over "
         f"{len(atom_names)} atoms {atom_names} …")
    formulas = gen_formulas(atom_names, max_nodes)
    note(f"HUNTER gave {len(formulas):,} formulas. Judging × all markings "
         f"on {cores} cores (chunk {chunk}) …")

    tasks = [(i, ch) for i, ch in enumerate(_chunks(formulas, chunk))]
    total = {b: 0 for b in BUCKETS}
    pairs = 0
    done = 0
    with Pool(cores) as pool:
        for cid, counts, p in pool.imap_unordered(_process, tasks):
            for b in BUCKETS:
                total[b] += counts[b]
            pairs += p
            done += 1
            el = time.time() - t0
            rate = pairs / el if el else 0
            note(f"chunk {done}/{len(tasks)}  pairs {pairs:,}  "
                 f"clean {total['clean']:,}  suspect {total['suspect']:,}  "
                 f"unverified {total['unverified']:,}  ({rate:,.0f}/s)")

    note("merging shards …")
    for b in BUCKETS:
        with open(os.path.join(RESULTS, f"{b}.jsonl"), "w") as out:
            for cid, _ in tasks:
                p = os.path.join(SHARDS, f"{b}.{cid}.jsonl")
                if os.path.exists(p):
                    with open(p) as f:
                        for line in f:
                            out.write(line)
    summary = {"atoms": atom_names, "max_nodes": max_nodes,
               "formulas": len(formulas), "pairs": pairs,
               "counts": total, "seconds": round(time.time() - t0, 1)}
    with open(os.path.join(RESULTS, "summary.json"), "w") as f:
        json.dump(summary, f, ensure_ascii=False, indent=2)
    note(f"DONE. pairs {pairs:,}  {total}  in {summary['seconds']}s")
    log.close()
    return summary


# ------------------------------------------------------------------ regression
def regression():
    """Pin the judge to zverify's MEASURED facts. The §5 trophy is NOT
    hereditary and is killed only at DEPTH 2 (b:=F, d:=F) — it survives every
    single verification, so it is not even sound (a completion gives F):
    grade 'until-verification', the deepest-hiding class. A §2 witness IS
    sound-but-not-hereditary → suspect. If either breaks, the judge diverged."""
    trophy = ("imp", ("xnor", "d", ("not", "c")),
              ("imp", ("imp", "b", "a"), ("xnor", "b", "c")))
    m = {"a": F, "b": "M", "c": "M", "d": "M"}
    v, grade, kill, depth = judge(trophy, m)
    assert v == T and grade != "hereditary", (v, grade)
    assert kill == {"b": F, "d": F} and depth == 2, (kill, depth)
    trophy_grade = grade
    # a §2 sound-but-not-hereditary cell: ¬¬p ∨ (q ∨ ¬q) — sound T, dies at p:=F
    soundcell = ("or", ("not", ("not", "p")), ("or", "q", ("not", "q")))
    sv, sg, sk, sd = judge(soundcell, {"p": "M", "q": "M"})
    assert sv == T and sg == "sound" and sk == {"p": F}, (sv, sg, sk)
    # the fallen law of identity at a marked atom → until-verification (F)
    iv, ig, ik, idp = judge(("imp", "p", "p"), {"p": "M"})
    assert iv == F and ig == "until-verification", (iv, ig)
    print(f"regression OK: trophy → {trophy_grade} (kill b=F,d=F, depth 2, "
          f"survives every single check); ¬¬p∨(q∨¬q) → suspect (sound, "
          f"kill p=F); p→p[mark] → unverified")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--atoms", default="a,b,c,d")
    ap.add_argument("--max-nodes", type=int, default=5)
    ap.add_argument("--cores", type=int, default=max(1, os.cpu_count() - 2))
    ap.add_argument("--chunk", type=int, default=500)
    ap.add_argument("--regression", action="store_true")
    a = ap.parse_args()
    if a.regression:
        regression()
    else:
        regression()
        run(a.atoms.split(","), a.max_nodes, a.cores, a.chunk)
