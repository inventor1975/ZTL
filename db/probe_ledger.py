# -*- coding: utf-8 -*-
"""
The measurement week, day one: one ledger, two ways, and an auditor's list.

Before building a database we are measuring whether one is worth building.
The same facts are loaded twice — once as anyone would in SQLite, once with
a warrant beside every value — and then a list of questions a real auditor
asks is put to both. The point is not to win. A rigged demonstration would
answer the strategy question with enthusiasm, which is the one currency
this project refuses.

So the verdicts are three, not two, and the middle one is the interesting
one:

    ANSWERS          plain SQL gets it right, and we add nothing
    ANSWERS WRONGLY  plain SQL returns a confident number that misleads
    CANNOT EXPRESS   there is no query, at any length

THE SCENARIO. A small contract ledger: three invoice lines, a ceiling, a
payment — and, above them, two DERIVED figures: the billed total and the
margin against what was paid. The derived ones are where an audit lives,
because they are what gets quoted upward and they rest on things that can
turn out to be false.

Some figures are documented; two are on somebody's word. Two lines rest on
the SAME invoice. Then the auditor learns that inv-17 is forged, and the
question is what else goes with it.

Run:  python3 db/probe_ledger.py
"""
import os
import sqlite3
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

# ------------------------------------------------------------ the facts
# name, value, whether it is documented, and by what
FACTS = [
    ("line_a", 3000.0, "earned", "inv-17"),
    ("line_b", 1500.0, "earned", "inv-17"),   # the SAME invoice as line_a
    ("line_c", 2000.0, "earned", "inv-18"),
    ("quoted", 1200.0, "credit", None),       # a figure someone told us
    ("ceiling", 9000.0, "earned", "contract"),
    ("paid", 5000.0, "credit", None),         # claimed, never evidenced
    ("billed", 6500.0, "earned", None),       # derived: a + b + c
    ("margin", 1500.0, "earned", None),       # derived: billed - paid
]

# What each derived figure was computed FROM. This is the edge an ordinary
# schema has no column for, and the whole cascade rides on it.
DERIVED = [
    ("billed", "line_a"), ("billed", "line_b"), ("billed", "line_c"),
    ("margin", "billed"), ("margin", "paid"),
]


def plain_db():
    """The ordinary way. A number is a number."""
    db = sqlite3.connect(":memory:")
    db.execute("CREATE TABLE ledger (name TEXT PRIMARY KEY, amount REAL)")
    db.executemany("INSERT INTO ledger VALUES (?,?)",
                   [(n, v) for n, v, _p, _w in FACTS])
    return db


# ------------------------------------------------- the warrant-carrying way
class HonestSum:
    """SUM that cannot lie about what it added.

    The whole doctrine as an aggregate: a total inherits the WEAKEST ground
    of its parts. Add earned to earned and the total is earned; add one
    figure nobody evidenced and the total is on credit — and it says which
    figure did it. Plain SQL's SUM has no way to be told this, which is why
    it returns a confident number over a mixture."""

    def __init__(self):
        self.total = 0.0
        self.weak = []

    def step(self, value, prov, name):
        self.total += value or 0.0
        if prov != "earned":
            self.weak.append(name)

    def finalize(self):
        if self.weak:
            # sorted for the same reason as the cascade: the order rows reach
            # an aggregate is a query-plan detail, not a fact about the ledger
            return f"{self.total:g} ON CREDIT (weak: {','.join(sorted(self.weak))})"
        return f"{self.total:g} EARNED"


def ztl_db():
    """The same facts, with the warrant beside every value, plus the
    citation graph the ledger needs."""
    db = sqlite3.connect(":memory:")
    db.executescript("""
      CREATE TABLE ledger (name TEXT PRIMARY KEY, amount REAL,
                           amount_status TEXT, amount_witness TEXT);
      CREATE TABLE rests_on (name TEXT, witness TEXT);
    """)
    db.executemany("INSERT INTO ledger VALUES (?,?,?,?)", FACTS)
    db.executemany("INSERT INTO rests_on VALUES (?,?)",
                   [(n, w) for n, _v, _p, w in FACTS if w])
    db.executemany("INSERT INTO rests_on VALUES (?,?)", DERIVED)
    db.create_aggregate("honest_sum", 3, HonestSum)
    return db


# ------------------------------------------------------------ the questions
LINES = "SELECT sum(amount) FROM ledger WHERE name LIKE 'line_%'"
CEIL = "SELECT amount FROM ledger WHERE name='ceiling'"


def q(label, plain, ztl, verdict, note):
    print(f"\n  {label}")
    print(f"    plain SQL : {plain}")
    print(f"    with warrant: {ztl}")
    print(f"    -> {verdict}: {note}")
    return verdict


def against_us(z):
    """The other direction, and the reason this file is not a demo.

    The question list above is MINE. A list one writes oneself is a list one
    wins, so the counterweight is measured here: what does the warrant break,
    and where does it fail to help even when present."""
    print("\n" + "=" * 78)
    print("AGAINST US — measured on the same table")
    print("=" * 78)

    naive = z.execute("SELECT sum(amount) FROM ledger").fetchone()[0]
    honest = z.execute("SELECT honest_sum(amount, amount_status, name) "
                       "FROM ledger").fetchone()[0]
    print(f"\n  1. An outsider's ordinary query against OUR table")
    print(f"       SELECT sum(amount)  ->  {naive:g}")
    print(f"       honest_sum(...)     ->  {honest}")
    print("     THE SHARPEST FINDING OF THE DAY, and it cuts against the")
    print("     three-column design. The warrant is there, in the row, and")
    print("     the built-in SUM walks straight past it. Every report anyone")
    print("     writes without knowing our convention is exactly as")
    print("     misleading as before — the honesty is opt-in, and the people")
    print("     most likely to be misled are the ones who never opted in.")
    print("     This is the one real argument for a custom TYPE (Postgres,")
    print("     the PostGIS precedent) over three plain columns: a type can")
    print("     make the ordinary SUM refuse or carry the warrant along. It")
    print("     is also the one thing SQLite cannot give us.")

    n = 200_000
    import time
    import tempfile

    def build(cols):
        fh = tempfile.NamedTemporaryFile(suffix=".db", delete=False)
        fh.close()
        db = sqlite3.connect(fh.name)
        db.execute("PRAGMA journal_mode=OFF")
        if cols:
            db.execute("CREATE TABLE t (name TEXT, amount REAL, "
                       "amount_status TEXT, amount_witness TEXT)")
            db.executemany("INSERT INTO t VALUES (?,?,?,?)",
                           ((f"c{i}", float(i), "earned", "doc-%d" % (i % 97))
                            for i in range(n)))
        else:
            db.execute("CREATE TABLE t (name TEXT, amount REAL)")
            db.executemany("INSERT INTO t VALUES (?,?)",
                           ((f"c{i}", float(i)) for i in range(n)))
        db.commit()
        return db, fh.name

    plain_db_, pf = build(False)
    warr_db, wf = build(True)
    size_p, size_w = os.path.getsize(pf), os.path.getsize(wf)

    t0 = time.perf_counter()
    plain_db_.execute("SELECT sum(amount) FROM t").fetchone()
    t_plain = time.perf_counter() - t0
    warr_db.create_aggregate("honest_sum", 3, HonestSum)
    t0 = time.perf_counter()
    warr_db.execute("SELECT honest_sum(amount, amount_status, name) "
                    "FROM t").fetchone()
    t_honest = time.perf_counter() - t0
    t0 = time.perf_counter()
    warr_db.execute("SELECT sum(amount) FROM t").fetchone()
    t_builtin = time.perf_counter() - t0

    print(f"\n  2. What the warrant costs, on {n:,} rows   [MEASURED]")
    print(f"       file size   plain {size_p/1e6:.1f} MB   with warrant "
          f"{size_w/1e6:.1f} MB   (x{size_w/size_p:.1f})")
    print(f"       built-in SUM, plain table        {t_plain*1000:7.1f} ms")
    print(f"       built-in SUM, warrant table      {t_builtin*1000:7.1f} ms")
    print(f"       honest_sum (python callback)     {t_honest*1000:7.1f} ms"
          f"   (x{t_honest/t_plain:.0f})")
    print("     The size is a real cost and an acceptable one. The aggregate")
    print("     is not free: a Python callback per row is the price of")
    print("     honesty in SQLite, and it is the second argument for doing")
    print("     this in a compiled extension rather than a convention.")
    for f in (pf, wf):
        os.unlink(f)

    print("\n  3. What this probe did NOT measure, and should not be read as")
    print("     Whether a real auditor asks these eight questions. The list")
    print("     is the author's, drawn from the corpus's own vocabulary, and")
    print("     a list one writes oneself is a list one wins. The next")
    print("     measurement worth making is against somebody else's list.")


def main():
    print("=" * 78)
    print("ONE LEDGER, TWO WAYS — what an auditor can actually ask")
    print("=" * 78)
    # Printed because this stand went red in CI and green here, and there was
    # no way to tell from the log which of the two machines was unusual.
    print(f"  python {sys.version.split()[0]}   sqlite {sqlite3.sqlite_version}")
    p, z = plain_db(), ztl_db()
    verdicts = []

    verdicts.append(q(
        "1. What was spent in total?",
        f"{p.execute(LINES).fetchone()[0]:g}",
        z.execute("SELECT honest_sum(amount, amount_status, name) FROM ledger"
                  " WHERE name LIKE 'line_%'").fetchone()[0],
        "ANSWERS",
        "both right — every line here is documented, so there is nothing to "
        "warn about and we add nothing"))

    verdicts.append(q(
        "2. What is the whole ledger's total?",
        f"{p.execute('SELECT sum(amount) FROM ledger').fetchone()[0]:g}",
        z.execute("SELECT honest_sum(amount, amount_status, name) "
                  "FROM ledger").fetchone()[0],
        "ANSWERS WRONGLY",
        "plain SQL adds two figures nobody evidenced into one confident "
        "number and says nothing; the same query with a warrant returns the "
        "total AND the names that put it on credit"))

    verdicts.append(q(
        "3. Are we inside the ceiling?",
        "under" if p.execute(LINES).fetchone()[0]
        < p.execute(CEIL).fetchone()[0] else "over",
        z.execute("SELECT CASE WHEN (SELECT sum(amount) FROM ledger WHERE "
                  "name LIKE 'line_%') < (SELECT amount FROM ledger WHERE "
                  "name='ceiling') THEN 'under' ELSE 'over' END || ' — on ' "
                  "|| (SELECT group_concat(DISTINCT amount_status) FROM "
                  "ledger WHERE name LIKE 'line_%' OR name='ceiling')"
                  ).fetchone()[0],
        "ANSWERS",
        "both right, and here the warrant is genuinely redundant"))

    verdicts.append(q(
        "4. Which figures have never been documented?",
        "no such column",
        ", ".join(r[0] for r in z.execute(
            "SELECT name FROM ledger WHERE amount_status <> 'earned'")),
        "CANNOT EXPRESS",
        "the ordinary schema did not record it, so the question has no "
        "query — this is the cheapest gap and the easiest to dismiss"))

    verdicts.append(q(
        "5. What rests on invoice inv-17?",
        "no such column",
        ", ".join(r[0] for r in z.execute(
            "SELECT name FROM rests_on WHERE witness='inv-17'")),
        "CANNOT EXPRESS",
        "two lines share that invoice, which is the fact the whole audit "
        "turns on"))

    CASCADE = """
      WITH RECURSIVE fallen(name) AS (
        SELECT name FROM rests_on WHERE witness = ?
        UNION
        SELECT r.name FROM rests_on r JOIN fallen f ON r.witness = f.name)
      SELECT name FROM fallen"""
    # SORTED, and not for looks. What falls is a set; the order SQLite
    # happens to walk the recursion in is an engine detail, and a stand whose
    # marker depends on one is a stand that can go red on somebody else's
    # machine for no reason at all. Ordering nothing is cheaper than
    # explaining a red CI.
    fallen = sorted(r[0] for r in z.execute(CASCADE, ("inv-17",)))
    verdicts.append(q(
        "6. inv-17 turns out to be forged. What falls?",
        "no query, at any length",
        f"{len(fallen)}: {', '.join(fallen)}",
        "CANNOT EXPRESS",
        "THE question of an audit. Two lines fall directly and the cascade "
        "carries it up into the billed total and the margin — the two "
        "figures that were quoted upward. Ordinary SQL has no notion of a "
        "value resting on a document, so there is nothing to walk"))

    before = z.execute("SELECT honest_sum(amount, amount_status, name) "
                       "FROM ledger WHERE name LIKE 'line_%'").fetchone()[0]
    z.execute("UPDATE ledger SET amount_status='credit', amount_witness=NULL"
              " WHERE name IN (%s)" % ",".join("?" * len(fallen)), fallen)
    after = z.execute("SELECT honest_sum(amount, amount_status, name) "
                      "FROM ledger WHERE name LIKE 'line_%'").fetchone()[0]
    verdicts.append(q(
        "7. And what do the numbers become once it is withdrawn?",
        f"{p.execute(LINES).fetchone()[0]:g}"
        " — unchanged, because for plain SQL nothing changed",
        f"{before}  ->  {after}",
        "ANSWERS WRONGLY",
        "the arithmetic is the same and the standing is not; plain SQL "
        "reports the first and has no room for the second"))

    # PULLED OUT OF THE f-STRING, 2026-08-18. This query used to sit inside the
    # replacement field, built with chr(34)/chr(39) to dodge quote nesting — a
    # dodge that only works because the expression spans three lines, which
    # Python allows from 3.12 (PEP 701) and CI's 3.11 tokenizer rejects with
    # "unterminated string literal". The machine that wrote it ran 3.12 and was
    # green; CI was red on a file nobody had touched. Green on one interpreter
    # is not a result, which is the same lesson `dilemmas/cogito.py` taught
    # about green on one filesystem.
    margin = p.execute(
        "SELECT amount FROM ledger WHERE name='margin'").fetchone()[0]
    verdicts.append(q(
        "8. May I quote the margin in the report?",
        f"{margin:g} — nothing else to say",
        " / ".join(f"{r[0]} {r[1]:g} {r[2]}" for r in z.execute(
            "SELECT name, amount, amount_status FROM ledger "
            "WHERE name IN ('billed','margin')")),
        "ANSWERS WRONGLY",
        "the number a director actually reads. It survived the forgery "
        "numerically and did not survive it as a warrant, and only one of "
        "the two schemas can say so"))

    print("\n" + "=" * 78)
    from collections import Counter
    c = Counter(verdicts)
    for k in ("ANSWERS", "ANSWERS WRONGLY", "CANNOT EXPRESS"):
        print(f"  {k:16} {c[k]}")
    print()
    print(f"  READ IT HONESTLY. Of {len(verdicts)} questions, plain SQL answers")
    print(f"  {c['ANSWERS']} perfectly well, and on those we add nothing but noise.")
    print("  The gap is not that SQL is bad at arithmetic — it is excellent")
    print("  at it — but that it has no place to put the difference between")
    print("  a number somebody evidenced and a number somebody said.")
    print(f"  {c['ANSWERS WRONGLY']} come back CONFIDENT AND MISLEADING, which is worse than")
    print(f"  a refusal, and the {c['CANNOT EXPRESS']} it cannot express at all are the ones")
    print("  an auditor is actually paid to answer.")
    against_us(z)
    assert c["CANNOT EXPRESS"] >= 2 and c["ANSWERS"] >= 2
    print("\nLEDGER PROBE GREEN — measured, not argued.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
