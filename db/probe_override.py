# -*- coding: utf-8 -*-
"""
The measurement week, day four: can an outsider's ordinary SUM be made honest?

Day one ended on the finding that cut against our own design. The warrant sat
in the row, and `SELECT sum(amount)` walked straight past it: the honesty was
opt-in, and whoever was most likely to be misled had never opted in. That was
left as the one real argument for a custom type in Postgres.

Postgres is not on this machine, so the type experiment is NOT run here and
nothing below should be read as having run it. What IS measurable is the
question underneath, and the answer turned out to be sitting in SQLite all
along: a user-defined aggregate may take the NAME of a built-in. `sum` can be
replaced. So the outsider writes the same query and gets a different answer.

That raises the real question, which is not "can we hijack sum" but "what does
sum get to see". A one-argument `sum(amount)` receives the amount and nothing
else. With the warrant in a neighbouring column it is structurally blind, no
matter who wrote the aggregate. It can only be honest if the warrant travels
INSIDE the value.

Which is a trade, not a win, and the trade is measured below.

Run:  python3 db/probe_override.py
"""
import os
import sqlite3
import sys
import time

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

# A PREDICTION THAT FAILED, and the way it failed is the finding.
# This list first held five amounts of four digits each, and the comparison
# test below came out IDENTICAL on both layouts — because for strings of
# equal length lexicographic order IS numeric order, so the defect had
# nowhere to show. A ledger with a two-figure petty item and a six-figure
# contract is the ordinary case, and the sample is now one: `petty` is here
# because a sample that cannot expose the fault is not a sample, it is a
# demonstration.
FACTS = [("line_a", 3000.0, "earned"), ("line_b", 1500.0, "earned"),
         ("line_c", 2000.0, "earned"), ("quoted", 1200.0, "credit"),
         ("petty", 750.0, "earned"), ("paid", 5000.0, "credit")]
TRUE_TOTAL = sum(v for _n, v, _s in FACTS)
WEAK = sorted(n for n, _v, s in FACTS if s != "earned")


class BlindSum:
    """Our aggregate, registered under the built-in's name, over a layout
    that keeps the warrant in its own column. It is honest by intention and
    blind by construction: one argument arrives, and it is the number."""

    def __init__(self):
        self.total = 0.0

    def step(self, value):
        self.total += value or 0.0

    def finalize(self):
        return f"{self.total:g} (and no idea what it added)"


class CarriedSum:
    """The same aggregate over values that carry their own warrant. Same
    query, same name, same single argument — and now it can refuse to
    present a mixed total as a clean one."""

    def __init__(self):
        self.total = 0.0
        self.weak = []

    def step(self, value):
        if isinstance(value, str) and "@" in value:
            num, status = value.rsplit("@", 1)
            self.total += float(num)
            if status != "earned":
                self.weak.append(num)
        else:                       # an ordinary number, left alone
            self.total += value or 0.0

    def finalize(self):
        if self.weak:
            return f"{self.total:g} ON CREDIT ({len(self.weak)} of the parts)"
        return f"{self.total:g} EARNED"


def split_layout():
    db = sqlite3.connect(":memory:")
    db.execute("CREATE TABLE ledger (name TEXT, amount REAL, status TEXT)")
    db.executemany("INSERT INTO ledger VALUES (?,?,?)", FACTS)
    return db


def carried_layout():
    db = sqlite3.connect(":memory:")
    db.execute("CREATE TABLE ledger (name TEXT, amount TEXT)")
    db.executemany("INSERT INTO ledger VALUES (?,?)",
                   [(n, f"{v:g}@{s}") for n, v, s in FACTS])
    return db


def main():
    print("=" * 78)
    print("CAN AN OUTSIDER'S `SELECT sum(amount)` BE MADE HONEST?")
    print("=" * 78)
    print(f"  python {sys.version.split()[0]}   sqlite {sqlite3.sqlite_version}")
    print(f"\n  The ledger: {TRUE_TOTAL:g} in total, of which the parts "
          f"{', '.join(WEAK)} rest on nobody's document.")

    q = "SELECT sum(amount) FROM ledger"

    print("\n  1. THE BUILT-IN, over the warrant-in-its-own-column layout")
    db = split_layout()
    print(f"       {q}  ->  {db.execute(q).fetchone()[0]:g}")
    print("     Day one's finding, unchanged: a confident number over a")
    print("     mixture, with nothing to mark it.")

    print("\n  2. OUR AGGREGATE, registered under the name `sum`")
    db.create_aggregate("sum", 1, BlindSum)
    print(f"       {q}  ->  {db.execute(q).fetchone()[0]}")
    print("     SQLite lets a user-defined aggregate take a built-in's name,")
    print("     so the hijack works and buys NOTHING. One argument arrives")
    print("     and it is the number. The status column is a foot away and")
    print("     entirely out of reach. No cleverness in the aggregate can")
    print("     fix this — it is the call signature, not the code.")

    print("\n  3. THE SAME AGGREGATE, over values that carry their warrant")
    db2 = carried_layout()
    db2.create_aggregate("sum", 1, CarriedSum)
    print(f"       {q}  ->  {db2.execute(q).fetchone()[0]}")
    print("     The outsider wrote the identical query and got an answer")
    print("     that cannot mislead. THIS is what the day was for, and the")
    print("     lesson is not about aggregates at all: what a function may")
    print("     be honest about is fixed by what the VALUE carries, long")
    print("     before anyone writes the function.")

    print("\n  4. WHAT THE TRADE COSTS — measured over every threshold")
    plain, carried = split_layout(), carried_layout()
    Q = "SELECT count(*) FROM ledger WHERE amount > %d"
    disagree = [th for th in range(100, 6001, 50)
                if plain.execute(Q % th).fetchone()[0]
                != carried.execute(Q % th).fetchone()[0]]
    print(f"       thresholds tried                      {len(range(100, 6001, 50))}")
    print(f"       thresholds where the two DISAGREE     {len(disagree)}")
    th = disagree[0]
    print(f"       e.g. amount > {th}: split says "
          f"{plain.execute(Q % th).fetchone()[0]}, carried says "
          f"{carried.execute(Q % th).fetchone()[0]}")
    print("     Text compares as text, so `750@earned` sorts above `5000`.")
    print("     Every ordinary comparison, index, MIN, MAX, AVG and join on")
    print("     that column is now wrong — and wrong WITHOUT RAISING, which")
    print("     is the worse half. We would have cured one misleading total")
    print("     by making every other query on the column misleading.")
    assert len(disagree) > 0

    n = 200_000
    for label, mk, agg in (("split, built-in sum", split_layout, None),
                           ("carried, our sum", carried_layout, CarriedSum)):
        d = sqlite3.connect(":memory:")
        if label.startswith("split"):
            d.execute("CREATE TABLE t (a REAL)")
            d.executemany("INSERT INTO t VALUES (?)",
                          ((float(i),) for i in range(n)))
        else:
            d.execute("CREATE TABLE t (a TEXT)")
            d.executemany("INSERT INTO t VALUES (?)",
                          ((f"{i}@earned",) for i in range(n)))
            d.create_aggregate("sum", 1, agg)
        t0 = time.perf_counter()
        d.execute("SELECT sum(a) FROM t").fetchone()
        print(f"       {label:22} {(time.perf_counter()-t0)*1000:7.1f} ms"
              f"   on {n:,} rows")

    print("\n  5. AND THE CEILING THIS DAY DID NOT CROSS")
    print("     A registered function lives on a CONNECTION, in one process.")
    print("     Open the same file in a BI tool, a spreadsheet driver or")
    print("     `sqlite3` at a shell and the built-in is back, whole. So the")
    print("     protection reaches applications that load our code and")
    print("     nobody else — which is opt-in again, moved one level down")
    print("     and no further.")
    print("     What would actually close it is a type living in the")
    print("     DATABASE rather than the client, so that every connection")
    print("     inherits it. That is the Postgres experiment, it is NOT RUN")
    print("     HERE — no server on this machine — and until it is, the")
    print("     claim `an outsider is protected` remains unmeasured.")

    print("\n  THE DAY'S OUTPUT, and it revises day one's recommendation.")
    print("  I recommended three columns for storage on the grounds that")
    print("  foreign queries keep working. That is still true and is now")
    print("  measured to be the SAME property that makes an outsider's sum")
    print("  incurable there: a value the neighbours can read is a value")
    print("  that arrives at a function alone. The two are one fact, and")
    print("  the choice cannot be had both ways in SQLite.")
    print("\nOVERRIDE PROBE GREEN — the hijack works and the layout decides.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
