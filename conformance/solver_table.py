# -*- coding: utf-8 -*-
"""
The solver over every shape of unknown — the last instrument to get a net.

`znumsolve` is the one that does not merely judge but SOLVES: given a claim
with an unknown, it narrows, eliminates, and hands back a value together
with the provenance the value inherited from the derivation. That last part
is why it wants a sweep of its own. A judge that answers wrongly is caught by
a wrong answer; a solver that answers rightly with the wrong PROVENANCE hands
you a number that looks earned and is not, which is the exact failure this
corpus exists to prevent and the exact failure a verdict-only check misses.

WHAT IS SWEPT. Every combination of: which quantity is unknown, the lattice
it is confined to, whether the known quantities are earned or on credit, and
the formula that ties them. For each, the whole answer — disposition,
whether anything was solved, how many quantities were pinned, the provenance
each solved value came out with, and the cures named when it did not solve.

THE PROVENANCE INVARIANT, checked on every case rather than sampled: a value
DERIVED from grounds that were not all earned may not come out earned. That
is the whole promise of the solver, and it is the sort of thing that survives
a refactor by luck rather than by design.

CEILING: characterizes, does not verify — same as the other tables.

Run:  python3 conformance/solver_table.py            (check against stored)
      python3 conformance/solver_table.py --update   (re-bless)
"""
import hashlib
import json
import os
import sys
from collections import Counter
from itertools import product

_ROOT = os.environ.get("ZTL_ROOT") or os.path.dirname(
    os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from znumjudge import parse_quantities                           # noqa: E402
from znumsolve import solve_claim                                # noqa: E402

STORE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                     "solver_table.json")

UNKNOWN = ["?", "[0,20]", "4"]
PROV = ["earned:doc", "credit"]
LATTICE = ["", " int", " decimal2", " frac3"]

FORMULAS = [
    "sum(x,x) == total",
    "sum(x,y) == total",
    "x <= total",
    "sum(x,y) <= total",
    "x == total",
]


def cases():
    for formula in FORMULAS:
        for ux, lx, px, py, pt in product(UNKNOWN, LATTICE, PROV, PROV, PROV):
            parts = [f"x={ux} {px}{lx}"]
            if "y" in formula:
                parts.append(f"y=? {py}")
            parts.append(f"total=10 {pt}")
            yield formula, ", ".join(parts)


def read(formula, data):
    try:
        q, m = parse_quantities(data)
        r = solve_claim(formula, q, m)
        solved = r.get("solved") or {}
        provs = sorted({v.get("prov", "?") for v in solved.values()})
        cures = sorted({c.split()[0] for c in (r.get("next_check") or [])})
        # a value is LAUNDERED if it comes out earned while a quantity it
        # was derived from is on credit. The solver records both, so this
        # is a read rather than a guess.
        bad = [n for n, v in solved.items()
               if v.get("prov") == "earned" and v.get("weak")]
        return ((r["disposition"], len(solved), ",".join(provs) or "-",
                 ",".join(cures) or "-"), bad)
    except Exception as exc:
        return (("!" + type(exc).__name__, 0, "-", "-"), [])


def sweep():
    h = hashlib.sha256()
    census, examples, total, laundered = Counter(), {}, 0, []
    for formula, data in cases():
        v, bad = read(formula, data)
        h.update(f"{formula}|{data}|{v}".encode())
        census[v] += 1
        examples.setdefault(v, (formula, data))
        total += 1
        # THE INVARIANT, and the first draft of it over-reached: it flagged
        # `credit` anywhere in the sheet, which condemned the ordinary and
        # correct case of an UNKNOWN quantity — whose `credit` is the
        # absence of a ground, not a bad one — being solved from earned
        # neighbours. The real rule reads what the solver records: earned
        # provenance while a source it derived from is on credit.
        if bad:
            laundered.append((formula, data, v, bad))
    rare = sorted((n, list(map(str, k)), list(examples[k]))
                  for k, n in census.items() if n <= max(2, total // 200))
    return (h.hexdigest()[:16],
            {" | ".join(map(str, k)): n for k, n in census.most_common()},
            rare, total, laundered)


def main():
    print("=" * 78)
    print("THE SOLVER'S TABLE — every shape of unknown, and its provenance")
    print("=" * 78)
    fp, census, rare, total, laundered = sweep()
    print(f"\n  cases swept: {total:,}   fingerprint: {fp}")
    print("\n  CENSUS — disposition | solved | provenance | cures:")
    for k, n in list(census.items())[:14]:
        print(f"    {k[:60]:60} {n:>5}")
    if len(census) > 14:
        print(f"    ... {len(census) - 14} more shapes")
    print(f"\n  THE PROVENANCE INVARIANT — a value derived from grounds that")
    print("  were not all earned may not come out earned. Checked on every")
    print(f"  case: {len(laundered)} laundered values")
    for f, d, v, bad in laundered[:5]:
        print(f"    {f}  ::  {d}  ->  {v}  laundered: {bad}")
    if laundered:
        print("  RED — a solved number wearing a provenance it did not earn is")
        print("  the failure this whole corpus is built to prevent.")
        return 1
    print("  None. The derivation carries its weakest ground through, on")
    print("  every case in the sweep and not only where a stand looked.")
    print("  This sweep's first run earned its keep: it found a genuine")
    print("  crash in `znumsolve` (a narrowed quantity keeps its ORIGINAL")
    print("  witness, and the code downstream read that witness text as the")
    print("  list of source QUANTITIES — `earned:doc` became a lookup of a")
    print("  quantity called `doc`). Beyond the crash it would have")
    print("  mis-attributed silently had a document ever been named like a")
    print("  quantity. The sources are now recorded where they are known.")
    print(f"\n  RARE SHAPES ({len(rare)}), the first five:")
    for n, k, ex in rare[:5]:
        print(f"    {' | '.join(k)[:56]:56} x{n}")
        print(f"      e.g. {ex[0]}  ::  {ex[1]}")

    stored = json.load(open(STORE, encoding="utf-8")) \
        if os.path.exists(STORE) else None
    if "--update" in sys.argv or stored is None:
        json.dump({"fingerprint": fp, "cases": total, "census": census,
                   "rare": rare}, open(STORE, "w", encoding="utf-8"),
                  indent=1, ensure_ascii=False)
        print(f"\n  TABLE WRITTEN — {STORE}")
        return 0
    if stored["fingerprint"] == fp:
        print(f"\n  MATCHES the stored table ({stored['cases']:,} cases).")
        print("\nSOLVER TABLE GREEN — the solver answers, and attributes, exactly")
        print("as it did when this table was blessed. With this one every")
        print("instrument in the corpus has a net: judge, book, passport,")
        print("propositional judge, solver.")
        return 0
    print(f"\n  FINGERPRINT MOVED: {stored['fingerprint']} -> {fp}")
    for k in sorted(set(stored["census"]) | set(census)):
        a, b = stored["census"].get(k, 0), census.get(k, 0)
        if a != b:
            print(f"    {k[:60]:60} {a:>5} -> {b:>5}")
    print("\n  RED — read the diff, decide whether it is the change you meant,")
    print("  then re-bless with --update.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
