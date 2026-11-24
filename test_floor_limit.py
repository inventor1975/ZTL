# -*- coding: utf-8 -*-
"""test_floor_limit — "the floor cannot read it" is not "there is nothing to read" (zfunc.FloorLimit, 2026-11-24).

    python3 test_floor_limit.py

Both sides: a value that EXISTS but lies past a series' reach is OPEN with the reason named (never E, never "measure");
a value that does not exist (ln of a negative, sqrt of a negative, a non-integer power of a negative) stays E. And tan's
period: tan(46) and tan(14) are read — the sign checked against the true values (-2.0866..., 7.2446...)."""
import math
import sys

from znumjudge import judge_sheet_claim, parse_quantities

FAILS, N = [], [0]


def disp(claim, sheet=""):
    q, m = parse_quantities(sheet) if sheet else ({}, {})
    return judge_sheet_claim(claim, q, m)


def check(cond, what):
    N[0] += 1
    if not cond:
        FAILS.append(what)
        print("FAIL", what)


# a limit: OPEN, the reason first in next_check, no "repair the claim"
r = disp("exp(60000) > 0")
check(r["disposition"] == "OPEN", "exp(60000) exists: OPEN, not E")
check(r["next_check"] and r["next_check"][0].startswith("the floor cannot read"), "the limit is named first")
check(not any(c.startswith("repair") for c in r["next_check"]), "no repair order for a value that exists")
# the other side: no value at all stays E
for c in ("ln(0-1) < 5", "sqrt(0-4) >= 0", "pow(0-2, 1/2) >= 0"):
    check(disp(c)["disposition"] == "E", f"{c}: no reading — E")
# tan's period, against the true values
assert math.tan(46) < 0 < math.tan(14)
check(disp("tan(46) < 0")["disposition"] == "EARNED", "tan(46) < 0 (true: -2.0866)")
check(disp("tan(46) > 0")["disposition"] == "REFUTED", "tan(46) > 0 refuted")
check(disp("tan(14) > 7")["disposition"] == "EARNED", "tan(14) > 7 (true: 7.2446)")
check(disp("tan(14) < 7")["disposition"] == "REFUTED", "tan(14) < 7 refuted")
check(disp("tan(0-46) > 0")["disposition"] == "EARNED", "tan(-46) = -tan(46) > 0")
check(disp("tan(1) > 1")["disposition"] == "EARNED", "tan(1) still read as before")
# a pole inside the box: undefined at a reading — a mark, not a value, not E
check(disp("tan(x) > -100", "x=[1,2] earned:a")["disposition"] == "OPEN", "a pole inside [1,2]: OPEN")
check(disp("sin(1000) <= 1")["disposition"] == "EARNED", "sin keeps its reduction")

# an UNDECIDED branch with no readings is a MARK, never E (2026-11-25): the other branch's readings exist
check(disp("ifpos(x, 1, sqrt(0 - 1)) == 1", "x=[-1,1] earned:a")["disposition"] == "OPEN", "undecided ifpos, a no-value branch: OPEN")
check(disp("ifpos(x, 1, sqrt(0 - 1)) == 1", "x=[1,2] earned:a")["disposition"] == "EARNED", "decided ifpos reads its branch only")
check(disp("ifpos(x, 1, sqrt(0 - 1)) == 1", "x=[-2,-1] earned:a")["disposition"] == "E", "decided into the no-value branch: E")

print(f"FLOOR LIMIT GREEN — {N[0]} checks" if not FAILS else f"test_floor_limit: {len(FAILS)} failures of {N[0]}")
sys.exit(1 if FAILS else 0)
