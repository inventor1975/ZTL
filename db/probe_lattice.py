# -*- coding: utf-8 -*-
"""
The measurement week, day three: the status column as a lattice point.

Day two found that ISA 500 ranks evidence along four independent axes, which
makes the ranking a lattice rather than a ladder, and that our two-valued
`earned` / `credit` collapses fifteen distinguishable qualities into one
word. This file does the obvious next thing — stores the lattice point
instead of the word — and then asks the only question that decides whether
the richer column is worth anything: DO ANY ANSWERS CHANGE.

They do, and not where expected. The interesting result is not that the
lattice is more expressive. It is that the two-valued column was hiding a
STIPULATION nobody wrote down — the line between earned and credit — and
the number of defensible places to draw that line turns out to be large
enough to measure.

Run:  python3 db/probe_lattice.py
"""
import itertools
import os
import sqlite3
import sys
import time

AXES = ("external", "documentary", "original", "direct")


def bits(g):
    """A lattice point as one integer, which is how a column would hold it."""
    return sum(v << i for i, v in enumerate(g))


def unbits(n):
    return tuple((n >> i) & 1 for i in range(4))


def name(g):
    on = [ax for ax, v in zip(AXES, g) if v]
    return "+".join(on) if on else "(nothing)"


def meet(a, b):
    return tuple(min(x, y) for x, y in zip(a, b))


# ------------------------------------------------------------------ the facts
# Yesterday's ledger, with each ground graded on ISA 500's four axes instead
# of being called earned or credit. The grading is the honest part of this
# file and the part a real accountant would correct — it is written down so
# that it CAN be corrected.
FACTS = [
    # name, amount, (external, documentary, original, direct), what it is
    ("line_a", 3000.0, (1, 1, 1, 0), "vendor's original invoice, held by us"),
    ("line_b", 1500.0, (1, 1, 0, 0), "a photocopy of that same invoice"),
    ("line_c", 2000.0, (1, 1, 1, 1), "invoice plus a confirmation the "
     "auditor obtained from the vendor directly"),
    ("quoted", 1200.0, (0, 0, 0, 0), "a figure a colleague mentioned"),
    ("ceiling", 9000.0, (1, 1, 1, 0), "the signed contract"),
    ("paid", 5000.0, (0, 1, 1, 0), "our own payment record, internal"),
]
DERIVED = [("billed", ["line_a", "line_b", "line_c"]),
           ("margin", ["billed", "paid"])]
GRADE = {n: g for n, _v, g, _d in FACTS}


def derive():
    """Derived figures inherit the MEET of their parts, which is the whole
    doctrine in one line: a total is no better evidenced than its worst
    ingredient, and on a lattice it can be worse than any of them."""
    for who, parts in DERIVED:
        g = (1, 1, 1, 1)
        for p in parts:
            g = meet(g, GRADE[p])
        GRADE[who] = g
    return GRADE


# ------------------------------------------------- part 1: does anything move
def part1():
    print("=" * 78)
    print("THE SAME LEDGER, GRADED ON SOMEBODY ELSE'S FOUR AXES")
    print("=" * 78)
    derive()
    print()
    for n in [f[0] for f in FACTS] + [d[0] for d in DERIVED]:
        kind = "derived" if n in dict(DERIVED) else ""
        print(f"    {n:9} {bits(GRADE[n]):2}  {name(GRADE[n]):45} {kind}")

    print("\n  The meet in action, and it is the case day two predicted:")
    a, b = GRADE["billed"], GRADE["paid"]
    assert meet(a, b) != a and meet(a, b) != b   # genuinely incomparable
    print(f"    billed  {name(a)}   (external, but only a photocopy in it)")
    print(f"    paid    {name(b)}   (original, but our own record)")
    print("    Neither dominates: one has the external axis, the other the")
    print("    original axis, and there is no fact of the matter about")
    print("    which is better evidence.")
    print(f"    margin  {name(GRADE['margin'])}")
    print("    The margin is worse evidence than EITHER of the figures it")
    print("    came from. A ladder cannot say this and a single number")
    print("    cannot either. This is the case that justifies the lattice,")
    print("    and it arose from an ordinary ledger without being staged.")
    assert GRADE["margin"] == (0, 1, 0, 0)


# ------------------------------- part 2: the stipulation the binary was hiding
def upsets():
    """Every defensible place to draw the earned/credit line.

    A threshold has to be UPWARD CLOSED: if a grade counts as earned, then
    any grade at least as good must too. Anything else is incoherent. The
    number of such thresholds on four axes is the Dedekind number M(4) —
    computed here rather than quoted, since quoting a number one has not
    checked is the exact habit this corpus exists to break."""
    grades = [unbits(i) for i in range(16)]
    out = []
    for mask in range(1 << 16):
        sel = {grades[i] for i in range(16) if mask >> i & 1}
        if all(not (g in sel and not (h in sel))
               for g in sel for h in grades
               if all(x >= y for x, y in zip(h, g))):
            out.append(sel)
    return out


def part2():
    print("\n" + "=" * 78)
    print("WHAT THE TWO-VALUED COLUMN WAS HIDING")
    print("=" * 78)
    t0 = time.perf_counter()
    ups = upsets()
    dt = time.perf_counter() - t0
    print(f"\n  coherent ways to draw the earned/credit line   {len(ups)}"
          f"   [computed, {dt:.1f}s]")
    print("  (the Dedekind number M(4) — every upward-closed set of grades)")

    # For each threshold, is the margin earned? And the billed total?
    for who in ("billed", "margin", "line_a"):
        yes = sum(1 for s in ups if GRADE[who] in s)
        print(f"\n    is `{who}` EARNED?   yes under {yes} thresholds, "
              f"no under {len(ups) - yes}")
    print("\n  THE FINDING. Yesterday's ledger called line_a `earned` and")
    print("  quoted the total as earned with it. That was not a fact about")
    print("  the invoice; it was a threshold the author picked without")
    print("  noticing he was picking one, out of 168 coherent choices. A")
    print("  two-valued status column does not remove the stipulation — it")
    print("  hides it, and hides it inside a word that reads like a")
    print("  measurement. That is the same offence as quoting a blast")
    print("  radius without its bracket, which this corpus already refuses")
    print("  (KNOWN-LIMITS, the reporting discipline).")
    print("\n  So the lattice point is not a luxury. Storing the grade and")
    print("  letting the READER apply a threshold puts the stipulation")
    print("  where it belongs: in the question, declared, not in the data,")
    print("  silent.")
    return len(ups)


# ------------------------------------------- part 3: can a column hold it well
def part3():
    print("\n" + "=" * 78)
    print("CAN A COLUMN HOLD IT — measured")
    print("=" * 78)
    n = 200_000
    import tempfile
    fh = tempfile.NamedTemporaryFile(suffix=".db", delete=False)
    fh.close()
    db = sqlite3.connect(fh.name)
    db.execute("PRAGMA journal_mode=OFF")
    db.execute("CREATE TABLE t (name TEXT, amount REAL, grade INTEGER, "
               "status TEXT)")
    db.executemany("INSERT INTO t VALUES (?,?,?,?)",
                   ((f"c{i}", float(i), i % 16,
                     "earned" if i % 16 == 15 else "credit")
                    for i in range(n)))
    db.commit()

    def timed(sql):
        t0 = time.perf_counter()
        r = db.execute(sql).fetchone()
        return (time.perf_counter() - t0) * 1000, r

    t_text, _ = timed("SELECT count(*) FROM t WHERE status='earned'")
    t_mask, r_mask = timed("SELECT count(*) FROM t WHERE grade & 3 = 3")
    db.execute("CREATE INDEX ix ON t(grade)")
    t_idx, _ = timed("SELECT count(*) FROM t WHERE grade = 15")
    db.execute("CREATE INDEX ix2 ON t((grade & 3))")
    t_expr, _ = timed("SELECT count(*) FROM t WHERE grade & 3 = 3")

    print(f"\n  on {n:,} rows                                    [MEASURED]")
    print(f"    status='earned'            (text)        {t_text:7.1f} ms")
    print(f"    grade & 3 = 3   (external AND documentary) {t_mask:7.1f} ms"
          f"   -> {r_mask[0]:,} rows")
    print(f"    grade = 15      (indexed, exact point)   {t_idx:7.1f} ms")
    print(f"    grade & 3 = 3   (expression index)       {t_expr:7.1f} ms")
    print("\n  A lattice point is four bits in an INTEGER. Every threshold")
    print("  is a bitmask test, every one of them indexable, and the")
    print("  column is SMALLER than the word it replaces. The richer")
    print("  vocabulary costs nothing in the store — which was the thing")
    print("  worth checking before recommending it, not after.")
    db.close()
    os.unlink(fh.name)


def main():
    part1()
    got = part2()
    part3()
    assert got == 168
    print("\nLATTICE PROBE GREEN — the column got richer and cheaper.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
