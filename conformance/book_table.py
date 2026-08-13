# -*- coding: utf-8 -*-
"""
The BOOK's behaviour over a systematic sweep — the net over the instrument
that actually needed one.

There is an irony worth stating plainly at the top of this file. The judge
table was built because the judge's behaviour had started coming out where
nobody predicted; it sweeps `znumjudge`. But every surprise of the session
that prompted it was in `zbook`: the strict reading caught direct withdrawal
and missed collapse, the clock field lied about arithmetic that was already
right, the quiet naming case opened no bracket, the parallel default came
out backwards. Four in one day, all in the ledger, and the ledger had no
sweep — only a six-case battery (`zbook.fingerprint`), which is a smoke
alarm in one room of the house.

WHAT IS SWEPT. Books are graphs, so they cannot be enumerated the way a
marking can; what is enumerated is a bounded FAMILY. Three claims, each
grounded in one of a vocabulary that covers every ground kind the book
distinguishes — a plain document, a shared document, a citation, a nullary
act, a clocked certificate, an alternative pair, an alternative pair sharing
an ancestor, and nothing at all. Every assignment, every book judged, and
the recorded answer is the whole of what the book says about itself:
dispositions, the assurance frame per claim, the trust brackets, the
declarations, and what the graph refutes.

That is 8^3 = 512 books over 3 formulas, which is small enough to be
exhaustive and wide enough that the failures of this session would each have
shown up in it. The point is not the count.

CEILING, the same as the judge table's: this CHARACTERIZES, it does not
verify. It records what the book does, including whatever it does wrongly.
Agreeing with it tomorrow proves that nothing moved unnoticed, which is the
whole and only job.

Run:  python3 conformance/book_table.py            (check against stored)
      python3 conformance/book_table.py --update   (re-bless)
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

from zbook import (judge_book, trust_interval, NotAMove)         # noqa: E402

STORE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                     "book_table.json")

# Every ground kind the book distinguishes, one of each. `claim/c0` makes a
# citation; `shared` gives two claims a common document; the last pair is
# the one whose independence the graph can refute.
GROUNDS = [
    "earned:doc-own",
    "earned:shared",
    "earned:claim/c0",
    "earned:performed/zero",
    "earned:expiring/cert",
    "earned:doc-a|doc-b",
    "earned:claim/c0|doc-b",
    "credit",
]

FORMULAS = ["x == 1", "x <= 5", "sum(x,y) == 2"]


def books():
    for formula in FORMULAS:
        second = ", y=1 earned:doc-own" if "y" in formula else ""
        for combo in product(GROUNDS, repeat=3):
            yield formula, combo, [
                (f"c{i}", formula, f"x=1 {g}{second}")
                for i, g in enumerate(combo)
            ]


def read(book):
    """Everything the book says about itself, flattened for hashing."""
    try:
        res = judge_book(book)
        iv = trust_interval(book)
    except NotAMove:
        return ("!NotAMove",)
    except Exception as exc:
        return ("!" + type(exc).__name__,)
    rows = []
    for cid in sorted(res):
        v = res[cid]
        a = v["assurance"]
        rows.append((cid, v["disposition"], a["tested"], a["under_learning"],
                     a["under_expiry"], len(v["declared"]),
                     len(v["not_independent"])))
    widths = sorted((lo, hi) for lo, hi in iv.values())
    return (tuple(rows), tuple(widths))


def sweep():
    h = hashlib.sha256()
    census, examples, total = Counter(), {}, 0
    for formula, combo, book in books():
        r = read(book)
        h.update(f"{formula}|{combo}|{r}".encode())
        # the census key is the SHAPE of the answer, not its detail: which
        # dispositions, which assurance axes, whether any bracket is wide
        if isinstance(r[0], str):                 # an error shape
            key = (r[0], "", "", "")
        else:
            rows, widths = r
            key = (",".join(sorted({x[1] for x in rows})),
                   ",".join(sorted({x[2] for x in rows})),
                   ",".join(sorted({x[4] for x in rows})),
                   "wide" if any(hi > lo for lo, hi in widths) else "tight")
        census[key] += 1
        examples.setdefault(key, (formula, combo))
        total += 1
    rare = sorted((n, list(k), list(map(str, examples[k])))
                  for k, n in census.items() if n <= max(2, total // 100))
    return (h.hexdigest()[:16],
            {" | ".join(k): n for k, n in census.most_common()}, rare, total)


def main():
    print("=" * 78)
    print("THE BOOK'S TABLE — every ground kind, in every position")
    print("=" * 78)
    fp, census, rare, total = sweep()
    print(f"\n  books swept: {total:,}   fingerprint: {fp}")
    print("\n  CENSUS — dispositions | tested | expiry | brackets:")
    for k, n in census.items():
        print(f"    {k:56} {n:>5}")
    print(f"\n  RARE SHAPES ({len(rare)}):")
    for n, k, ex in rare:
        print(f"    {' | '.join(k):56} x{n}")
        print(f"      e.g. {ex[0]}  ::  {ex[1]}")

    stored = json.load(open(STORE, encoding="utf-8")) \
        if os.path.exists(STORE) else None
    if "--update" in sys.argv or stored is None:
        json.dump({"fingerprint": fp, "books": total, "census": census,
                   "rare": rare}, open(STORE, "w", encoding="utf-8"),
                  indent=1, ensure_ascii=False)
        print(f"\n  TABLE WRITTEN — {STORE}")
        return 0
    if stored["fingerprint"] == fp:
        print(f"\n  MATCHES the stored table ({stored['books']:,} books).")
        print("\nBOOK TABLE GREEN — the ledger answers exactly as it did when")
        print("this table was blessed. The judge got its sweep first; the")
        print("book is where every surprise of the day actually happened, and")
        print("it now has one too.")
        return 0
    print(f"\n  FINGERPRINT MOVED: {stored['fingerprint']} -> {fp}")
    for k in sorted(set(stored["census"]) | set(census)):
        a, b = stored["census"].get(k, 0), census.get(k, 0)
        if a != b:
            print(f"    {k:56} {a:>5} -> {b:>5}")
    print("\n  RED — the ledger answers differently than when this table was")
    print("  blessed. Read the diff, decide whether it is the change you")
    print("  meant, then re-bless with --update.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
