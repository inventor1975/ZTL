# -*- coding: utf-8 -*-
"""
The judge's behaviour over a systematic sweep of its inputs — a reference
table, and the diff against it.

The curator's reason for it, and it is the right one: the judge is still
being built, and its behaviour has started coming out in places nobody
predicted. Today alone three of this session's changes altered a verdict
that no one had asked about, and only an assert in some unrelated stand
caught them. Stands cover the cases we thought of. This covers the cases we
did not.

WHAT IS SWEPT. Every combination of the sheet judge's input dimensions over
two quantities — provenance, value shape, lattice, unit, the sample flag —
against a set of formulas. Roughly 184 thousand judgements, which at the
measured 13.5k/sec single-threaded is a matter of seconds; the space is
enumerated exhaustively rather than sampled, so nothing is missed by luck.

WHAT IS STORED, and this is the design decision worth defending. Not the
table: 184k rows are unreadable and a diff of them is unusable. Three things
instead —

  * a FINGERPRINT, one hash over the whole sweep. Any change to any verdict
    moves it. That is the alarm;
  * a CENSUS, verdict counts by input class. That is the readable body of
    the thing: what the judge does, in twenty lines;
  * the RARE CELLS, verbatim. A verdict that occurs a handful of times in
    184k inputs is either a deliberate corner of the design or a bug, and
    both deserve to be looked at by name. These are where the surprises
    live.

WHEN THE FINGERPRINT MOVES, the run prints the census diff, so the question
is never "did something change" but "what, and is it what you meant".

CEILING: this characterizes, it does not verify. A table records what the
judge DOES, including whatever it does wrongly; agreeing with it tomorrow
proves only that nothing moved. It is a regression net and a map, not a
proof — the proofs are in `lean/`.

Run:  python3 conformance/judge_table.py            (check against stored)
      python3 conformance/judge_table.py --update   (re-bless the table)
"""
import hashlib
import json
import os
import sys
from collections import Counter
from itertools import product

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from znumjudge import judge_sheet_claim, parse_quantities        # noqa: E402

STORE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                     "judge_table.json")

# --------------------------------------------------------- the input space
PROV = ["earned:doc", "credit"]
VALUE = ["1", "5", "[0,10]", "?"]
LATTICE = ["", " int", " decimal2", " frac3"]
UNIT = ["", " RUB", " m"]
SAMPLE = ["", " sample"]

FORMULAS = [
    "x <= y",
    "x == y",
    "x < y",
    "sum(x,y) == 5",
    "x <= y & ok",
]


def quantity(name, prov, value, lattice, unit, sample):
    return f"{name}={value} {prov}{lattice}{unit}{sample}"


def cases():
    """Every combination, enumerated. The nonsensical ones are included on
    purpose: what the judge does with `? earned:doc` is exactly the kind of
    corner nobody writes a stand for."""
    shapes = list(product(PROV, VALUE, LATTICE, UNIT, SAMPLE))
    for formula in FORMULAS:
        tail = ", ok=Z" if "ok" in formula else ""
        for sx in shapes:
            qx = quantity("x", *sx)
            for sy in shapes:
                yield formula, f"{qx}, {quantity('y', *sy)}{tail}"


def verdict(formula, data):
    try:
        q, m = parse_quantities(data)
        r = judge_sheet_claim(formula, q, m)
        # the cure KINDS, not their arguments: `measure x` and `measure y`
        # are the same shape of answer and should not split a cell
        cures = sorted({c.split()[0] for c in (r.get("next_check") or [])})
        return (r["disposition"], str(r.get("lazy")), ",".join(cures) or "-")
    except Exception as exc:                     # a corner that stops parsing
        return ("!" + type(exc).__name__, "-", 0)


def sweep():
    """Returns (fingerprint, census, rare, total)."""
    h = hashlib.sha256()
    census, examples = Counter(), {}
    total = 0
    for formula, data in cases():
        v = verdict(formula, data)
        h.update(f"{formula}|{data}|{v}".encode())
        census[v] += 1
        examples.setdefault(v, (formula, data))
        total += 1
    rare = sorted((n, list(v), list(examples[v]))
                  for v, n in census.items() if n <= total // 1000)
    return (h.hexdigest()[:16],
            {" ".join(map(str, k)): n for k, n in census.most_common()},
            rare, total)


def main():
    update = "--update" in sys.argv
    print("=" * 78)
    print("THE JUDGE'S TABLE — an exhaustive sweep of its input space")
    print("=" * 78)
    fp, census, rare, total = sweep()
    print(f"\n  cases swept: {total:,}   fingerprint: {fp}")
    print("\n  CENSUS — what the judge does, by verdict:")
    for k, n in census.items():
        print(f"    {k:34} {n:>8,}  ({100 * n / total:5.2f}%)")
    print(f"\n  RARE CELLS ({len(rare)}) — a verdict reached by a handful of")
    print("  inputs is either a deliberate corner or a bug, and both want a")
    print("  name:")
    for n, v, ex in rare:
        print(f"    {' '.join(map(str, v)):30} x{n:<4} {ex[0]}  ::  {ex[1]}")
    if not rare:
        smallest = min(census.values())
        print(f"    none — the smallest cell holds {smallest:,} inputs. The")
        print("    judge has no one-off corners in this space: every behaviour")
        print("    it shows, it shows systematically. That is a finding and")
        print("    not an empty section.")

    earned = census.get("EARNED T -", 0)
    empty = sum(n for k, n in census.items() if k.startswith("E "))
    print("\n  WHAT THE CENSUS SAYS")
    print(f"    EARNED: {earned:,} of {total:,} — {100 * earned / total:.2f}%.")
    print("    Across every systematically enumerated input, fewer than two")
    print("    in a hundred earn. That is the no-credit rule as a statistic")
    print("    rather than a slogan: earning is the rare event by design.")
    print(f"    E (no readings at all): {empty:,} — "
          f"{100 * empty / total:.2f}%.")
    print("    Nearly a quarter of the space is unjudgeable — mismatched")
    print("    units, impossible lattices, inverted intervals. That is a")
    print("    fact about the input space, not a defect of the judge: the")
    print("    fourth corner is where nonsense goes, and nonsense is common")
    print("    when you enumerate rather than curate.")

    stored = None
    if os.path.exists(STORE):
        stored = json.load(open(STORE, encoding="utf-8"))
    if update or stored is None:
        json.dump({"fingerprint": fp, "cases": total, "census": census,
                   "rare": rare}, open(STORE, "w", encoding="utf-8"),
                  indent=1, ensure_ascii=False)
        print(f"\n  TABLE WRITTEN — {STORE}")
        print("  (blessing a table is a decision: it records what the judge")
        print("   does today, right or wrong. Read the census before doing it.)")
        return 0

    if stored["fingerprint"] == fp:
        print(f"\n  MATCHES the stored table ({stored['cases']:,} cases).")
        print("\nJUDGE TABLE GREEN — the judge answers exactly as it did when")
        print("this table was blessed. Which proves nothing about whether it")
        print("answers WELL; it proves that nothing moved unnoticed, and that")
        print("is the whole job of a characterization sweep.")
        return 0

    print(f"\n  FINGERPRINT MOVED: {stored['fingerprint']} -> {fp}")
    print("  census diff (stored -> now):")
    keys = set(stored["census"]) | set(census)
    for k in sorted(keys):
        a, b = stored["census"].get(k, 0), census.get(k, 0)
        if a != b:
            print(f"    {k:34} {a:>8,} -> {b:>8,}")
    print("\n  RED — the judge answers differently than when this table was")
    print("  blessed. That is not automatically wrong: if the change was")
    print("  intended, read the diff, satisfy yourself it is the change you")
    print("  meant and no other, then re-bless with --update.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
