# -*- coding: utf-8 -*-
"""
judge_worst — the slowest claims for the judge after the 2026-09-27 speed-up.

Families of claims built to defeat `zverify._only` (atoms repeated so folding
cannot collapse them) and to load the rest of the judge (the `_joint` probes,
the bearing probe of numeric atoms, the reverse pass `what_to_check`), at a
given number of atoms as `zfl.validate` counts them. Each candidate is timed
in CPU seconds, in-process, under a CPU budget (ITIMER_VIRTUAL): a case that
exceeds it is recorded as `> budget`, never waited for.

  judge   ztljudge.judge(claim, marking)          the verdict + warranty alone
  run     zfl.run(doc), zfl.validate stubbed      what the studio does

Run:
  python3 inventory/probes/judge_worst.py shapes --sizes 10,12,14 --budget 20
  python3 inventory/probes/judge_worst.py climb --family xorcycle --n 10 --steps 200
  python3 inventory/probes/judge_worst.py one --json '{"claim": ..., "rows": [...]}'
Everything is seeded: family F at n atoms, variant k, is random.Random(f"{F}:{n}:{k}").
"""
import argparse
import json
import os
import random
import signal
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, ROOT)

import zfl                                    # noqa: E402
import ztljudge                               # noqa: E402

_VALIDATE = zfl.validate


class OverBudget(BaseException):
    pass


def _alarm(signum, frame):
    raise OverBudget()


signal.signal(signal.SIGVTALRM, _alarm)


def timed(fn, budget):
    """CPU seconds of fn(), or None if it ran past `budget` CPU seconds."""
    signal.setitimer(signal.ITIMER_VIRTUAL, budget)
    t = time.process_time()
    try:
        out = fn()
        return time.process_time() - t, out
    except OverBudget:
        return None, None
    except Exception as e:                    # noqa: BLE001 — a refusal, recorded
        return time.process_time() - t, {"_error": type(e).__name__}
    finally:
        signal.setitimer(signal.ITIMER_VIRTUAL, 0)


# ------------------------------------------------ the proposed `_lazy` fix
# NOT a change to the core: an in-process stand-in used only when `--fix-lazy`
# is given, to measure what the caps would be once `ztljudge._lazy` stops
# evaluating an implication's children twice (line 292 evaluates both
# children of every binary node; the `imp` branch then re-reads the node as
# `~a | b` and evaluates both again, so each nested `->` doubles the work).
# The same computation, from the values already in hand.
T_, F_, Z_ = "T", "F", "Z"


def lazy_fixed(phi, m):
    if isinstance(phi, str):
        if phi in (T_, F_, Z_):
            return phi, set()
        v = m.get(phi, Z_)
        return (v, {phi}) if v == Z_ else (v, set())
    op = phi[0]
    if op == "not":
        v, lab = lazy_fixed(phi[1], m)
        return ({T_: F_, F_: T_, Z_: Z_}[v], lab)
    (a, la), (b, lb) = lazy_fixed(phi[1], m), lazy_fixed(phi[2], m)
    if op == "imp":
        a = {T_: F_, F_: T_, Z_: Z_}[a]          # ~a, label unchanged
        op = "or"
    if op == "and":
        if a == F_:
            return F_, la
        if b == F_:
            return F_, lb
        return (T_, set()) if a == b == T_ else (Z_, la | lb)
    if op == "or":
        if a == T_:
            return T_, la
        if b == T_:
            return T_, lb
        return (F_, set()) if a == b == F_ else (Z_, la | lb)
    if op in ("xnor", "xor"):
        if Z_ in (a, b):
            return Z_, la | lb
        same = (a == b)
        return (T_ if (same if op == "xnor" else not same) else F_), set()
    raise ValueError(op)


_LAZY_ORIG = ztljudge._lazy


def use_fixed_lazy(on):
    ztljudge._lazy = lazy_fixed if on else _LAZY_ORIG


# ------------------------------------------------------------ the documents
OPS = ["&", "|", "^", "->", "<->"]


def atoms_names(n):
    return [f"a{i}" for i in range(n)]


def rows_for(names, rnd, mix):
    if isinstance(mix, int):                    # exactly `mix` unverified
        rows = []
        unv = set(rnd.sample(names, min(mix, len(names))))
        for a in names:
            st = "unverified" if a in unv else rnd.choice(["verified", "refuted"])
            row = {"name": a, "means": a, "status": st}
            if st != "unverified":
                row["ground"] = f"doc-{a}"
            rows.append(row)
        return rows
    return _rows_mixed(names, rnd, mix)


def _rows_mixed(names, rnd, mix):
    """Rows for the plain atoms. mix: 'unverified' (all), or 'mixed' —
    unverified / verified / refuted / defined over earlier rows."""
    rows = []
    for i, a in enumerate(names):
        st = "unverified"
        if mix == "mixed":
            st = rnd.choice(["unverified", "unverified", "verified", "refuted", "defined"])
            if st == "defined" and i < 2:
                st = "unverified"
        row = {"name": a, "means": a, "status": st}
        if st in ("verified", "refuted"):
            row["ground"] = f"doc-{a}"
        if st == "defined":
            x, y = rnd.sample(names[:i], 2)
            row["ground"] = f"{x} {rnd.choice(['&', '|', '^', '->', '<->'])} {y}"
        rows.append(row)
    return rows


def fam_random(n, rnd):
    names = atoms_names(n)
    pool = list(names)
    rnd.shuffle(pool)

    def gen(k):                       # k leaves; each atom at least once
        if k == 1:
            return pool.pop() if pool else rnd.choice(names)
        j = rnd.randint(1, k - 1)
        e = f"({gen(j)} {rnd.choice(OPS)} {gen(k - j)})"
        return "~" + e if rnd.random() < 0.1 else e
    return gen(n + rnd.randint(0, n)), names


def fam_xorcycle(n, rnd):
    """(a0 op a1) op' (a1 op a2) op' ... (a_{n-1} op a0): every atom twice,
    op from {^, <->} so no constant folds a pair away."""
    names = atoms_names(n)
    parts = [f"({names[i]} {rnd.choice(['^', '<->'])} {names[(i + 1) % n]})" for i in range(n)]
    e = parts[0]
    for p in parts[1:]:
        e = f"({e} {rnd.choice(['&', '|', '^', '<->', '->'])} {p})"
    return e, names


def fam_repeat(n, rnd):
    """Each atom 2-4 times, shuffled, joined by xor / biconditional."""
    names = atoms_names(n)
    leaves = [a for a in names for _ in range(rnd.randint(2, 4))]
    rnd.shuffle(leaves)
    e = leaves[0]
    for x in leaves[1:]:
        e = f"({e} {rnd.choice(['^', '<->', '^', '&', '|'])} {x})"
    return e, names


def fam_grid(n, rnd):
    """Atoms on a ring-grid; each edge (ai <-> aj) or (ai ^ aj), edges joined
    by & / |: each atom 3-4 times."""
    names = atoms_names(n)
    edges = []
    for i in range(n):
        for d in (1, 3):
            edges.append(f"({names[i]} {rnd.choice(['^', '<->'])} {names[(i + d) % n]})")
    rnd.shuffle(edges)
    e = edges[0]
    for x in edges[1:]:
        e = f"({e} {rnd.choice(['&', '|', '->'])} {x})"
    return e, names


def fam_impchain(n, rnd):
    """(((a0 -> a1) -> a2) -> ... ): nested implications, each atom once or
    more, depth ~ 2n. The shape that doubles `_lazy`'s work per level."""
    names = atoms_names(n)
    e = names[0]
    for i in range(1, 2 * n):
        e = f"({e} -> {names[i % n]})"
    return e, names


def fam_long(n, rnd, length=4000):
    """A left-deep chain of random connectives over n atoms, grown to about
    `length` characters (the formula cap is 4096)."""
    names = atoms_names(n)
    e, i = names[0], 1
    while len(e) < length - 40:
        e = f"({e} {rnd.choice(OPS)} {names[i % n]})"
        i += 1
    return e, names


def fam_longbal(n, rnd, length=4000):
    """A balanced random tree over n atoms, about `length` characters."""
    names = atoms_names(n)
    k = max(n, length // 9)
    pool = [names[i % n] for i in range(k)]
    rnd.shuffle(pool)

    def gen(lo, hi):
        if hi - lo == 1:
            return pool[lo]
        mid = rnd.randint(lo + 1, hi - 1)
        return f"({gen(lo, mid)} {rnd.choice(OPS)} {gen(mid, hi)})"
    return gen(0, k), names


FAMILIES = {"random": fam_random, "xorcycle": fam_xorcycle,
            "repeat": fam_repeat, "grid": fam_grid, "impchain": fam_impchain,
            "long": fam_long, "longbal": fam_longbal}


def numeric_doc(n, rnd, shape):
    """n comparisons over x in [0,50] (each one Z), joined by the shape's
    operators; `repeat_text` repeats ONE comparison text n times (the cap
    counts comparison texts; the core reads one atom per occurrence)."""
    if shape == "repeat_text":
        cmps = ["(x <= 7)"] * n
    else:
        cmps = [f"(x <= {j + 1})" for j in range(n)]
    ops = {"xor": ["^"], "mixed": ["^", "<->", "&", "|", "->"]}[
        "mixed" if shape in ("mixed", "repeat_text") else "xor"]
    e = cmps[0]
    for c in cmps[1:]:
        e = f"({e} {rnd.choice(ops)} {c})"
    rows = [{"name": "x", "means": "x", "status": "unverified", "value": "[0,50]"}]
    return {"claim": e, "rows": rows}


def prop_doc(claim, names, rnd, mix):
    return {"claim": claim, "rows": rows_for(names, rnd, mix)}


def marking_of(doc):
    return zfl.resolved_marking(zfl.coerce(doc)["rows"])


# ------------------------------------------------------------ measurements
def measure(doc, budget, what=("judge", "run")):
    """{'judge': s|None, 'run': s|None, 'atoms': counted as validate counts}."""
    out = {}
    a, c = zfl._reading_atoms(doc["claim"])
    for r in doc["rows"]:
        if r.get("status") == "defined":
            a2, c2 = zfl._reading_atoms(r.get("ground") or "")
            a |= a2
            c |= c2
    out["atoms"] = len(a) + len(c)
    numeric = any(r.get("value") for r in doc["rows"])
    if "judge" in what and not numeric:
        m = marking_of(doc)
        out["judge"], r = timed(lambda: ztljudge.judge(zfl.normalise(doc["claim"], doc["rows"]), m), budget)
        if r and "_error" in r:
            out["judge_error"] = r["_error"]
        elif r:
            out["verdict"] = [r["verdict"], r["grade"], r["disposition"]]
    if "run" in what:
        zfl.validate = lambda d: []
        try:
            out["run"], r = timed(lambda: zfl.run(doc), budget)
        finally:
            zfl.validate = _VALIDATE
        if r and not r.get("ok", True):
            out["run_refused"] = [i.get("code") for i in r.get("issues", [])][:3]
        if r and r.get("report"):
            rep = r["report"]
            j = rep.get("judge") or rep.get("numeric") or {}
            out["run_disp"] = j.get("disposition")
    return out


def score(m):
    """Slowness for ranking: an over-budget case beats every finite one."""
    vals = [v for k, v in m.items() if k in ("judge", "run")]
    return max((float("inf") if v is None else v) for v in vals) if vals else 0.0


# ------------------------------------------------------------ search modes
def shapes(sizes, variants, budget, out, fams=None, mixes=("unverified", "mixed")):
    res = []
    for n in sizes:
        for fam in (fams or FAMILIES):
            if fam not in FAMILIES:
                continue                      # e.g. "numeric": handled below
            fn = FAMILIES[fam]
            for mix in mixes:
                worst = None
                for k in range(variants):
                    rnd = random.Random(f"{fam}:{mix}:{n}:{k}")
                    claim, names = fn(n, rnd)
                    doc = prop_doc(claim, names, rnd, mix)
                    m = measure(doc, budget)
                    if worst is None or score(m) > score(worst[0]):
                        worst = (m, doc)
                rec = {"family": fam, "mix": mix, "n": n, **worst[0], "doc": worst[1]}
                res.append(rec)
                print(f"  n={n:2d} {fam:9s} {str(mix):10s} atoms={rec['atoms']:2d} "
                      f"judge={_f(rec.get('judge'))} run={_f(rec.get('run'))}"
                      f"{' REFUSED ' + str(rec.get('run_refused')) if rec.get('run_refused') else ''}"
                      f"{' judge-error ' + rec['judge_error'] if rec.get('judge_error') else ''}",
                      flush=True)
        for shape in (("xor", "mixed", "repeat_text")
                      if not fams or "numeric" in fams else ()):
            worst = None
            for k in range(variants):
                rnd = random.Random(f"num-{shape}:{n}:{k}")
                doc = numeric_doc(n, rnd, shape)
                m = measure(doc, budget, what=("run",))
                if worst is None or score(m) > score(worst[0]):
                    worst = (m, doc)
            rec = {"family": f"numeric-{shape}", "mix": "-", "n": n, **worst[0], "doc": worst[1]}
            res.append(rec)
            print(f"  n={n:2d} numeric-{shape:11s}      atoms={rec['atoms']:2d} "
                  f"run={_f(rec.get('run'))}", flush=True)
    if out:
        json.dump(res, open(out, "w"), indent=1)
    return res


def _f(v):
    return " >budget" if v is None else ("   -   " if v == "" else f"{v:7.3f}")


def mutate(claim, names, rnd):
    """One structural edit of the claim text: swap an operator, replace an
    atom by another (repeat it), or wrap a subterm in a negation."""
    toks = claim.replace("(", " ( ").replace(")", " ) ").split()
    i = rnd.randrange(len(toks))
    for _ in range(20):
        i = rnd.randrange(len(toks))
        if toks[i] in OPS or toks[i] in names or toks[i].lstrip("~") in names:
            break
    t = toks[i]
    if t in OPS:
        toks[i] = rnd.choice([o for o in OPS if o != t])
    elif t.lstrip("~") in names:
        toks[i] = rnd.choice(names) if rnd.random() < 0.8 else "~" + t.lstrip("~")
    out = " ".join(toks).replace("( ", "(").replace(" )", ")")
    # every atom must still occur (the atom count stays n)
    if not all(any(tok.lstrip("~") == a for tok in out.replace("(", " ").replace(")", " ").split())
               for a in names):
        return claim
    return out


def climb(family, n, mix, steps, budget, seed, out):
    """Hill-climb on `run` CPU from the slowest of 20 seeded starts."""
    rnd = random.Random(f"climb:{family}:{mix}:{n}:{seed}")
    best = None
    for k in range(20):
        r2 = random.Random(f"{family}:{mix}:{n}:{k}")
        claim, names = FAMILIES[family](n, r2)
        doc = prop_doc(claim, names, r2, mix)
        m = measure(doc, budget)
        if best is None or score(m) > score(best[0]):
            best = (m, doc, names)
    print(f"  start: {score(best[0]):.3f} s", flush=True)
    for s in range(steps):
        m0, doc0, names = best
        claim = mutate(doc0["claim"], names, rnd)
        if claim == doc0["claim"]:
            continue
        doc = dict(doc0, claim=claim)
        m = measure(doc, budget)
        if score(m) > score(m0):
            best = (m, doc, names)
            print(f"  step {s}: {score(m):.3f} s  judge={_f(m.get('judge'))} "
                  f"run={_f(m.get('run'))}", flush=True)
    res = {"family": family, "mix": mix, "n": n, **best[0], "doc": best[1]}
    if out:
        json.dump(res, open(out, "w"), indent=1)
    print(json.dumps(res)[:600])
    return res


def lenscan(us, lengths, variants, budget, out, family="longbal"):
    """zfl.run CPU as a function of u (unverified atoms, the rest verified or
    refuted) and of the claim's length, 10 atoms: the reverse pass
    `what_to_check` runs for u <= 6 and calls judge ~1400 times at u = 6."""
    res = {}
    print("u \\ chars " + "".join(f"{L:>9d}" for L in lengths))
    for u in us:
        row = []
        for L in lengths:
            worst = 0.0
            for k in range(variants):
                rnd = random.Random(f"lenscan:{family}:{u}:{L}:{k}")
                claim, names = FAMILIES[family](10, rnd, L)
                doc = prop_doc(claim, names, rnd, u)
                m = measure(doc, budget, what=("run",))
                if m.get("run_refused"):
                    worst = max(worst, 0.0)
                    continue
                worst = max(worst, float("inf") if m["run"] is None else m["run"])
            row.append(worst)
            res[f"{u}:{L}"] = worst
        print(f"u={u:<2d}      " + "".join(" >budget " if v == float("inf") else f"{v:9.3f}"
                                         for v in row), flush=True)
    if out:
        json.dump(res, open(out, "w"), indent=1)
    return res


def judgescan(ns, lengths, variants, budget, out, family="longbal"):
    """judge() CPU, every atom unverified (the reverse pass does not run),
    as a function of the atom count and the claim's length: where
    `zverify._only` pays for atoms that occur many times."""
    res = {}
    print("n \\ chars " + "".join(f"{L:>9d}" for L in lengths))
    for n in ns:
        row = []
        for L in lengths:
            worst = 0.0
            for k in range(variants):
                rnd = random.Random(f"judgescan:{family}:{n}:{L}:{k}")
                claim, names = FAMILIES[family](n, rnd, L)
                m = {a: "Z" for a in names}
                t, r = timed(lambda: ztljudge.judge(claim, m), budget)
                if r and "_error" in r:
                    continue
                worst = max(worst, float("inf") if t is None else t)
            row.append(worst)
            res[f"{n}:{L}"] = worst
        print(f"n={n:<3d}     " + "".join(" >budget " if v == float("inf") else f"{v:9.3f}"
                                        for v in row), flush=True)
    if out:
        json.dump(res, open(out, "w"), indent=1)
    return res


def impdepth(depths, budget):
    """W1: k nested `->` over ONE atom — judge() and the REAL zfl.run (the
    validator and its cap in force), as-is and with the proposed _lazy fix."""
    print("depth chars   judge as-is   run as-is (real)   judge fixed   run fixed (real)")
    for k in depths:
        e = "a"
        for _ in range(k):
            e = f"({e} -> a)"
        doc = {"claim": e, "rows": [{"name": "a", "means": "a", "status": "unverified"}]}
        assert not [i for i in zfl.validate(doc) if i["level"] == "error"]
        cells = []
        for fixed in (False, True):
            use_fixed_lazy(fixed)
            tj, _ = timed(lambda: ztljudge.judge(e, {}), budget)
            tr, _ = timed(lambda: zfl.run(doc), budget)
            cells += [tj, tr]
        use_fixed_lazy(False)
        print(f"{k:5d} {len(e):5d} " + "".join(" >budget " if c is None else f"{c:10.3f}   "
                                              for c in cells), flush=True)


def epoch(counts, budget):
    """W3: declared expiry events on rows the claim never reads, REAL zfl.run."""
    claim, names = fam_grid(10, random.Random("epoch"))
    for n_ev in counts:
        rows = [{"name": a, "means": a, "status": "unverified"} for a in names]
        for i in range(n_ev):
            rows.append({"name": f"g{i}", "means": "g", "status": "verified",
                         "ground": f"doc-{i}", "expires_on": f"ev{i}"})
            rows.append({"name": f"ev{i}", "means": "an event", "status": "unverified"})
        doc = {"claim": claim, "rows": rows}
        errs = [i["code"] for i in zfl.validate(doc) if i["level"] == "error"]
        t, r = timed(lambda: zfl.run(doc), budget)
        kb = len(json.dumps({"doc": doc})) // 1024
        print(f"{n_ev:5d} events  {kb:4d} KB  validate errors {errs}  zfl.run "
              f"{'>budget' if t is None else f'{t:.2f} s'}", flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["shapes", "climb", "one", "lenscan", "judgescan",
                                     "impdepth", "epoch"])
    ap.add_argument("--depths", default="12,14,16,18,20,22")
    ap.add_argument("--events", default="0,50,200,800")
    ap.add_argument("--ns", default="8,10,12,14,16,20")
    ap.add_argument("--us", default="1,2,3,4,5,6")
    ap.add_argument("--lengths", default="100,250,500,1000,2000,4000")
    ap.add_argument("--sizes", default="10,12,14")
    ap.add_argument("--variants", type=int, default=8)
    ap.add_argument("--budget", type=float, default=20.0)
    ap.add_argument("--family", default="xorcycle")
    ap.add_argument("--mix", default="unverified")
    ap.add_argument("--n", type=int, default=10)
    ap.add_argument("--steps", type=int, default=200)
    ap.add_argument("--seed", default="20260927")
    ap.add_argument("--json", default=None)
    ap.add_argument("--fix-lazy", action="store_true",
                    help="measure with the proposed _lazy fix (in-process stand-in)")
    ap.add_argument("--families", default=None)
    ap.add_argument("--mixes", default="unverified,mixed,6")
    ap.add_argument("--out", default=None)
    a = ap.parse_args()
    use_fixed_lazy(a.fix_lazy)
    if a.mode == "shapes":
        fams = a.families.split(",") if a.families else list(FAMILIES)
        mixes = [int(x) if x.isdigit() else x for x in a.mixes.split(",")]
        shapes([int(x) for x in a.sizes.split(",")], a.variants, a.budget, a.out,
               fams, mixes)
    elif a.mode == "impdepth":
        impdepth([int(x) for x in a.depths.split(",")], a.budget)
    elif a.mode == "epoch":
        epoch([int(x) for x in a.events.split(",")], a.budget)
    elif a.mode == "judgescan":
        judgescan([int(x) for x in a.ns.split(",")], [int(x) for x in a.lengths.split(",")],
                  a.variants, a.budget, a.out)
    elif a.mode == "lenscan":
        lenscan([int(x) for x in a.us.split(",")], [int(x) for x in a.lengths.split(",")],
                a.variants, a.budget, a.out)
    elif a.mode == "climb":
        climb(a.family, a.n, a.mix, a.steps, a.budget, a.seed, a.out)
    else:
        doc = json.loads(a.json)
        print(json.dumps(measure(doc, a.budget)))


if __name__ == "__main__":
    main()
