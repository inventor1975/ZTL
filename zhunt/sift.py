# -*- coding: utf-8 -*-
"""
sift — turn the raw suspect corpus into a readable catalogue of DISTINCT broken
laws, ranked by treachery.

The hunter's suspect.jsonl is millions of records, most of them the same law
wearing different atom letters (`(b⊕a)→(c→c)`, `(b⊕a)→(d→d)`, …). This sifts:

  1. keep v=T (a genuine classical tautology) and depth ≥ 2 (survives ≥1 check);
  2. parse each formula, canonicalise atoms by first appearance → one key per
     law up to renaming, collapsing the duplicates;
  3. keep the minimal representative, aggregate depth / count / an example kill;
  4. flag the GUARD→GAP signature — an implication whose conclusion hides a
     "gap": a subformula that is a classical tautology yet greedy-F under total
     ignorance (the fallen-lemma shape, how a bad lemma sneaks past review);
  5. rank by (max depth ↓, nodes ↑, frequency ↓) — the deepest, simplest,
     commonest first.

Reads the parent core untouched.
"""

import json
import os
import sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from ztl import T, F, ev, VALUES                       # noqa: E402
from zmodal import ztl_eval                            # noqa: E402

SIGN = {"∧": "and", "∨": "or", "→": "imp", "⊕": "xor", "↔": "xnor"}
ASCII = {"and": "∧", "or": "∨", "imp": "→", "xor": "⊕", "xnor": "↔"}


# --------------------------------------------------------------- parse show()
def parse(s):
    """Parse a show()-formatted formula (fully parenthesised) into a tuple."""
    pos = 0

    def term():
        nonlocal pos
        c = s[pos]
        if c == "¬":
            pos += 1
            return ("not", term())
        if c == "(":
            pos += 1
            left = term()
            while s[pos] == " ":
                pos += 1
            op = SIGN[s[pos]]; pos += 1
            while s[pos] == " ":
                pos += 1
            right = term()
            while s[pos] == " ":
                pos += 1
            assert s[pos] == ")", s
            pos += 1
            return (op, left, right)
        j = pos
        while j < len(s) and s[j].isalpha():
            j += 1
        atom = s[pos:j]; pos = j
        return atom

    return term()


# --------------------------------------------------------------- canonicalise
def _atoms_in_order(phi, acc):
    if isinstance(phi, str):
        if phi not in acc:
            acc.append(phi)
    else:
        for x in phi[1:]:
            _atoms_in_order(x, acc)
    return acc


def _rename(phi, mp):
    if isinstance(phi, str):
        return mp[phi]
    return (phi[0],) + tuple(_rename(x, mp) for x in phi[1:])


def canonical(phi):
    """Rename atoms by first appearance to a,b,c,… → alpha-canonical form."""
    order = _atoms_in_order(phi, [])
    mp = {a: chr(ord("a") + i) for i, a in enumerate(order)}
    return _rename(phi, mp), mp


def nodes(phi):
    return 1 if isinstance(phi, str) else 1 + sum(nodes(x) for x in phi[1:])


def show(phi):
    if isinstance(phi, str):
        return phi
    if phi[0] == "not":
        return "¬" + show(phi[1])
    return "(" + show(phi[1]) + " " + ASCII[phi[0]] + " " + show(phi[2]) + ")"


# ----------------------------------------------------------- the GUARD→GAP eye
def _subforms(phi):
    yield phi
    if isinstance(phi, tuple):
        for x in phi[1:]:
            yield from _subforms(x)


def _atoms(phi, acc=None):
    acc = set() if acc is None else acc
    if isinstance(phi, str):
        acc.add(phi)
    else:
        for x in phi[1:]:
            _atoms(x, acc)
    return acc


def is_gap(g):
    """A gap: classical tautology, yet greedy-F when all its atoms are marked."""
    ats = sorted(_atoms(g))
    if not ats:
        return False
    from itertools import product
    for combo in product((T, F), repeat=len(ats)):
        if ev(g, dict(zip(ats, combo))) != T:
            return False                          # not a classical tautology
    return ztl_eval(g, {a: "M" for a in ats}) == F    # greedy-F under ignorance


def guard_gap(phi):
    """True if phi = (guard → conclusion) and the conclusion buries a gap."""
    if not (isinstance(phi, tuple) and phi[0] == "imp"):
        return False
    return any(is_gap(s) for s in _subforms(phi[2]))


# --------------------------------------------------------------------- sift
def sift(path, min_depth=2, top=40):
    laws = defaultdict(lambda: {"count": 0, "dmax": 0, "dmin": 99,
                                "kill": None, "rep": None, "nodes": 0})
    kept = 0
    for line in open(path):
        r = json.loads(line)
        if r["v"] != T or r["depth"] is None or r["depth"] < min_depth:
            continue
        kept += 1
        phi = parse(r["f"])
        can, mp = canonical(phi)
        key = show(can)
        d = laws[key]
        d["count"] += 1
        d["dmax"] = max(d["dmax"], r["depth"])
        d["dmin"] = min(d["dmin"], r["depth"])
        if d["rep"] is None:
            d["rep"] = can
            d["nodes"] = nodes(can)
            # kill is in the record's original atom names; map to canonical
            d["kill"] = {mp[a]: v for a, v in r["kill"].items()} \
                if r["kill"] else None
    rows = []
    for key, d in laws.items():
        rows.append((key, d, guard_gap(d["rep"])))
    rows.sort(key=lambda x: (-x[1]["dmax"], x[1]["nodes"], -x[1]["count"]))
    return kept, len(laws), rows[:top]


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("path", nargs="?",
                    default=os.path.join(HERE, "results", "suspect.jsonl"))
    ap.add_argument("--min-depth", type=int, default=2)
    ap.add_argument("--top", type=int, default=40)
    a = ap.parse_args()
    kept, distinct, rows = sift(a.path, a.min_depth, a.top)
    print(f"kept {kept:,} records (v=T, depth≥{a.min_depth}) → "
          f"{distinct:,} DISTINCT laws (up to renaming)\n")
    print(f"{'#':>3}  {'dmax':>4} {'n':>3} {'count':>8}  gap  law")
    for i, (key, d, gg) in enumerate(rows, 1):
        tag = "GAP" if gg else "   "
        print(f"{i:>3}  {d['dmax']:>4} {d['nodes']:>3} {d['count']:>8}  {tag}  "
              f"{key}   [kill {d['kill']}]")
