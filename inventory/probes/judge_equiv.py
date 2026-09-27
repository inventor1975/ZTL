# -*- coding: utf-8 -*-
"""
judge_equiv — does a tree of ZTL judge exactly like another? (2026-09-27)

Runs a seeded stream of claims through the judge of ONE source tree and prints
one digest per claim (the sha1 of the whole output, keys sorted). Two trees are
equivalent on the stream when their digest files are byte-identical; the
companion `--compare` names the first claims where they are not.

Two kinds of claim, both whole-output:
  prop   ztljudge.judge(text, marking): a random formula over up to 10 atoms
         (the studio's cap), connectives & | ^ -> = ~, depth <= 6, constants
         T/F/Z, and a random marking over T/F/Z/E (atoms left out read as Z).
         The output compared is the judge's entire dict: verdict, grade,
         disposition, why, unverified, absent, pending, lazy, joint, forgone.
  doc    zfl.run(doc): a studio table with 1-3 numeric names, their values,
         statuses and scales, and a claim of numeric comparisons joined by
         connectives, within the validator's cap (it runs, the cap included).
         The output compared is the whole report.

Run:
  python3 inventory/probes/judge_equiv.py --tree . --kind prop --start 0 --n 1000
  python3 inventory/probes/judge_equiv.py --compare OLD.txt NEW.txt
Each line: `<index> <sha1>`. Seeds: claim i of kind K is random.Random(f"{K}:{i}").
"""
import argparse
import hashlib
import json
import os
import random
import sys

OPS = ["&", "|", "^", "->", "="]
ATOMS = [f"a{i}" for i in range(10)]


def gen_formula(rnd, depth, atoms):
    if depth == 0 or rnd.random() < 0.18:
        r = rnd.random()
        return rnd.choice("TFZ") if r < 0.06 else rnd.choice(atoms)
    if rnd.random() < 0.2:
        return "~" + gen_formula(rnd, depth - 1, atoms)
    return (f"({gen_formula(rnd, depth - 1, atoms)} {rnd.choice(OPS)} "
            f"{gen_formula(rnd, depth - 1, atoms)})")


def prop_claim(i):
    rnd = random.Random(f"prop:{i}")
    k = rnd.choice([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 3, 4, 5, 6])
    atoms = ATOMS[:k]
    text = gen_formula(rnd, rnd.randint(1, 6), atoms)
    marks = {}
    for a in atoms:
        r = rnd.random()
        if r < 0.55:
            continue                              # left out: reads as Z
        marks[a] = rnd.choice(["T", "F", "Z", "Z", "E"])
    return text, marks


def doc_claim(i):
    rnd = random.Random(f"doc:{i}")
    names = ["x", "y", "z"][:rnd.randint(1, 3)]
    rows = []
    for n in names:
        lo = rnd.randint(-10, 10)
        hi = lo + rnd.choice([0, 1, 3, 10, 50])
        val = str(lo) if lo == hi else f"[{lo},{hi}]"
        st = rnd.choice(["unverified", "unverified", "verified"])
        row = {"name": n, "means": n, "status": st, "value": val,
               "scale": rnd.choice(["", "", "int", "decimal2", "frac3"])}
        if st == "verified":
            row["ground"] = f"doc-{n}"
        rows.append(row)
    ncmp = rnd.randint(1, 8)
    parts = []
    for _ in range(ncmp):
        a = rnd.choice(names)
        e = rnd.choice([a, f"{a} * {rnd.choice(names)}", f"{a} + {rnd.randint(-3, 3)}",
                        f"{a} - {rnd.choice(names)}"])
        parts.append(f"({e} {rnd.choice(['<=', '<', '>=', '>', '=='])} {rnd.randint(-5, 30)})")
    claim = parts[0]
    for p in parts[1:]:
        claim = f"{claim} {rnd.choice(['&', '|', '^', '->'])} {p}"
        if rnd.random() < 0.2:
            claim = f"~({claim})"
    return {"claim": claim, "rows": rows}


def digest(obj):
    return hashlib.sha1(json.dumps(obj, sort_keys=True, default=str,
                                   ensure_ascii=False).encode()).hexdigest()


def run(tree, kind, start, n, out):
    sys.path.insert(0, os.path.abspath(tree))
    if kind == "prop":
        import ztljudge
        for i in range(start, start + n):
            text, marks = prop_claim(i)
            try:
                r = ztljudge.judge(text, marks)
            except Exception as e:                  # the same refusal is equivalence too
                r = {"exception": type(e).__name__, "msg": str(e)}
            out.write(f"{i} {digest(r)}\n")
    else:
        import zfl
        for i in range(start, start + n):
            doc = doc_claim(i)
            try:
                r = zfl.run(doc)
            except Exception as e:
                r = {"exception": type(e).__name__, "msg": str(e)}
            out.write(f"{i} {digest(r)}\n")


def compare(a, b):
    la, lb = open(a).read().split("\n"), open(b).read().split("\n")
    la, lb = [x for x in la if x], [x for x in lb if x]
    diff = [(x, y) for x, y in zip(la, lb) if x != y]
    print(f"{a}: {len(la)} lines, {b}: {len(lb)} lines, differing: {len(diff)}")
    for x, y in diff[:10]:
        print("  ", x, "|", y)
    return len(la) == len(lb) and not diff


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tree", default=".")
    ap.add_argument("--kind", choices=["prop", "doc"], default="prop")
    ap.add_argument("--start", type=int, default=0)
    ap.add_argument("--n", type=int, default=1000)
    ap.add_argument("--compare", nargs=2, default=None)
    a = ap.parse_args()
    if a.compare:
        sys.exit(0 if compare(*a.compare) else 1)
    run(a.tree, a.kind, a.start, a.n, sys.stdout)


if __name__ == "__main__":
    main()
