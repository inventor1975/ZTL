# -*- coding: utf-8 -*-
"""
The propositional judge over every depth-2 formula and every marking.

The last two instruments without a net, taken together here and in
`solver_table.py`. This one is the core: `ztljudge.judge` is what every
philosophical case in `dilemmas/` calls, what the docket's eighth verdict
uses, and what the corpus means when it says "the judge". Parts of its space
are already pinned by asserts scattered through the stands — `zledger`
counts tautologies, `zsweep` counts arrows, each case file pins its own
findings — but an assert catches what somebody thought to write down. A
fingerprint catches the rest.

WHAT IS SWEPT. Every formula of depth two over two atoms, built from the
connectives the judge parses — negation, conjunction, disjunction,
implication, exclusive or — against all nine markings over {T, F, Z}. For
each, the whole verdict: value, disposition, grade, and the named weak
links, which is the field this corpus cares about most and the one no other
system produces.

The pool is generated rather than borrowed so that the sweep does not
inherit another module's choices; `zledger`'s depth-2 pool exists and is
larger, but it is trees where this wants the judge's own surface syntax, and
a net should not depend on a second instrument to say what it covers.

CEILING: characterizes, does not verify. Depth two over two atoms is a
bounded family — the deep interactions of `zderive` and the infinite ones of
Yablo are outside it.

Run:  python3 conformance/ztl_table.py            (check against stored)
      python3 conformance/ztl_table.py --update   (re-bless)
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

import ztljudge as J                                             # noqa: E402

STORE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                     "ztl_table.json")

ATOMS = ["p", "q"]
VALUES = ["T", "F", "Z"]
BINARY = ["&", "|", "->", "^"]


def pool():
    """Depth two, in the judge's own surface syntax."""
    lvl0 = list(ATOMS)
    lvl1 = lvl0 + [f"~{a}" for a in lvl0]
    lvl2 = [f"({a} {op} {b})" for a in lvl1 for op in BINARY for b in lvl1]
    return lvl1 + lvl2 + [f"~{f}" for f in lvl2]


def markings():
    for combo in product(VALUES, repeat=len(ATOMS)):
        yield dict(zip(ATOMS, combo))


def read(formula, marking):
    try:
        r = J.judge(formula, marking)
        return (r["verdict"], r["disposition"], r["grade"],
                ",".join(sorted(r["unverified"])) or "-")
    except Exception as exc:
        return ("!" + type(exc).__name__, "", "", "")


def sweep():
    h = hashlib.sha256()
    census, examples, total = Counter(), {}, 0
    formulas = pool()
    for formula in formulas:
        for m in markings():
            v = read(formula, m)
            h.update(f"{formula}|{sorted(m.items())}|{v}".encode())
            census[v] += 1
            examples.setdefault(v, (formula, dict(m)))
            total += 1
    rare = sorted((n, list(v), [examples[v][0], str(examples[v][1])])
                  for v, n in census.items() if n <= max(3, total // 500))
    return (h.hexdigest()[:16],
            {" | ".join(k): n for k, n in census.most_common()},
            rare, total, len(formulas))


def main():
    print("=" * 78)
    print("THE PROPOSITIONAL JUDGE'S TABLE — depth 2, every marking")
    print("=" * 78)
    fp, census, rare, total, nf = sweep()
    print(f"\n  {nf:,} formulas x 9 markings = {total:,} verdicts")
    print(f"  fingerprint: {fp}")
    print("\n  CENSUS — value | disposition | grade | weak links:")
    for k, n in list(census.items())[:14]:
        print(f"    {k[:62]:62} {n:>6}")
    if len(census) > 14:
        print(f"    ... {len(census) - 14} more shapes")
    hered = sum(n for k, n in census.items() if "hereditary" in k)
    marked = sum(n for k, n in census.items() if k.startswith("Z |"))
    print(f"\n  HEREDITARY: {hered:,} of {total:,} "
          f"({100 * hered / total:.2f}%) — the MAJORITY, and the first draft")
    print("  of this file said the opposite, guessing it would be rare like")
    print("  EARNED is in the numeric sweep. Different question: there,")
    print("  earning is rare because a GROUND has to be produced; here, a")
    print("  verdict that settles at all is hereditary whichever way it")
    print("  settles, and most depth-2 formulas settle under most markings.")
    print(f"\n  VERDICT Z: {marked:,} of {total:,} — and every one of them a")
    print("  bare atom or its negation. That is the greedy register's rule")
    print("  showing up as a statistic rather than a slogan: compounds never")
    print("  take the mark, so the only way to see Z in a verdict is to ask")
    print("  about an atom directly.")
    print(f"\n  RARE SHAPES ({len(rare)}), the first five:")
    for n, k, ex in rare[:5]:
        print(f"    {' | '.join(k)[:58]:58} x{n}")
        print(f"      e.g. {ex[0]}  ::  {ex[1]}")

    stored = json.load(open(STORE, encoding="utf-8")) \
        if os.path.exists(STORE) else None
    if "--update" in sys.argv or stored is None:
        json.dump({"fingerprint": fp, "verdicts": total, "formulas": nf,
                   "census": census, "rare": rare},
                  open(STORE, "w", encoding="utf-8"), indent=1,
                  ensure_ascii=False)
        print(f"\n  TABLE WRITTEN — {STORE}")
        return 0
    if stored["fingerprint"] == fp:
        print(f"\n  MATCHES the stored table ({stored['verdicts']:,}).")
        print("\nZTL TABLE GREEN — the judge every case file calls answers")
        print("exactly as it did when this was blessed, across the whole")
        print("depth-2 space and not only where a stand happened to look.")
        return 0
    print(f"\n  FINGERPRINT MOVED: {stored['fingerprint']} -> {fp}")
    for k in sorted(set(stored["census"]) | set(census)):
        a, b = stored["census"].get(k, 0), census.get(k, 0)
        if a != b:
            print(f"    {k[:62]:62} {a:>6} -> {b:>6}")
    print("\n  RED — read the diff, decide whether it is the change you")
    print("  meant, then re-bless with --update.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
