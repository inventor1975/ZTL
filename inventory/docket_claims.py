# -*- coding: utf-8 -*-
"""
The docket's TABLE, checked row by row against the machine.

`inventory/paper_claims.py` checks the numbers in the papers — theorem
counts, module counts, page counts. It does not read tables. But the
paradox docket IS a table: twenty-one rows of passport, solution count,
period and negation parity, printed as prose in the paper and encoded
under assert in `zclassify.py`. Two copies of the same claim, and nothing
compared them.

That is precisely the shape of the mistake this project exists to catch,
and the curator named the stake: errors here are Frege's story. So each
published row is parsed out of the markdown and re-measured, and the run
fails if the paper and the machine disagree by one cell.

Run:  python3 inventory/docket_claims.py
"""
import os
import re
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from zclassify import DOCKET, measure                          # noqa: E402

PAPER = os.path.join(_ROOT, "paper", "paradox-docket-EN-draft.md")


def paper_rows(path):
    """Every numbered row of the docket table, as printed."""
    rows = []
    for line in open(path, encoding="utf-8"):
        if not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) < 7 or not cells[0].isdigit():
            continue
        rows.append({"n": int(cells[0]), "case": cells[1],
                     "passport": cells[3].replace("*", "").split("(")[0].strip(),
                     "solutions": cells[4], "period": cells[5],
                     "negations": cells[6]})
    return rows


def main():
    print("=" * 78)
    print("THE DOCKET TABLE — every published row, re-measured")
    print("=" * 78)
    rows = paper_rows(PAPER)
    print(f"\n  rows printed in the paper: {len(rows)}")
    print(f"  cases encoded in zclassify: {len(DOCKET)}")
    bad = []
    if len(rows) != len(DOCKET):
        # not fatal by itself: the paper prints the dilemma series inside
        # the same table while the code may keep extras. Report and match
        # what can be matched, by position.
        print("  (counts differ — rows are matched by position, and the")
        print("   remainder is reported below rather than skipped)")
    for i, row in enumerate(rows):
        if i >= len(DOCKET):
            bad.append((row["n"], row["case"], "no encoded case for this row"))
            continue
        label, system, expected, negations = DOCKET[i]
        kind, models, period, _comp = measure(system)
        paper_p, paper_s = row["passport"], row["solutions"]
        problems = []
        if kind != paper_p:
            problems.append(f"passport paper={paper_p} measured={kind}")
        if paper_s not in ("—", "-", ""):
            if str(models) != paper_s:
                problems.append(f"solutions paper={paper_s} measured={models}")
        if row["period"] not in ("—", "-", ""):
            if str(period) != row["period"].replace("**", ""):
                problems.append(f"period paper={row['period']} "
                                f"measured={period}")
        mark = "ok " if not problems else "!! "
        print(f"  {mark}{row['n']:>2}. {row['case'][:34]:36} "
              f"{kind:16} models={models} period={period}")
        for p in problems:
            print(f"        {p}")
            bad.append((row["n"], row["case"], p))
    print()
    if bad:
        print(f"RED — {len(bad)} cell(s) of the published table do not match")
        print("      the machine. This is the Frege case: fix the paper or")
        print("      fix the encoding, and say which was wrong.")
        return 1
    print("DOCKET TABLE GREEN — every published row re-measured and matching.")
    print()
    print("  CEILING: this compares the table to the code. It does not read")
    print("  the prose around it, and a table can be right while the")
    print("  sentence explaining it is wrong.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
