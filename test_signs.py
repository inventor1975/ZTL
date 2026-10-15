"""A sign after an operator (`x - -19`, `a * -b`) is the operand's sign, not a subtraction.

Found 2026-10-13 by the ztl-stand soundness audit: Python's ast.unparse writes `x0 - -19`, and _parse_arith split at
the second minus, leaving an empty side ("malformed arithmetic: ''") on seven fuzz bricks. Each spelling below is
read and its value checked exactly against Python's own reading of the same text.

Run: python3 test_signs.py
"""
import sys
from fractions import Fraction as F

from znumjudge import _parse_arith

FAILS = []


def value(t):
    if isinstance(t, F):
        return t
    op, a, b = t
    a, b = value(a), value(b)
    return {"add": a + b, "sub": a - b, "mul": a * b, "div": a / b}[op]


CASES = ["7 - -19", "3 * -2", "8 / -2", "-3 - -4", "2 - -3 * 4", "1 - 2 - 3", "2 * 3 - -1", "(-1) - (-2)",
         "-5 + 20", "10 - - 2", "1 + -2 + 3", "6 / -3 / 2", "2 * (3 - -4)", "4 - -(2 - 5)", "1 - 2 + 3 - 4"]
for e in CASES:
    try:
        got = value(_parse_arith(e, {}))
    except Exception as x:          # noqa: BLE001 — every failure is reported, none skipped
        FAILS.append(f"{e!r}: {type(x).__name__}: {x}")
        continue
    want = F(eval(e.replace("/", "*F(1)/")))                     # exact: Fractions all the way
    if got != want:
        FAILS.append(f"{e!r}: read as {got}, Python reads {want}")

for f in FAILS:
    print("  FAIL", f)
if FAILS:
    print(f"SIGNS RED: {len(FAILS)} of {len(CASES)}")
    sys.exit(1)
print(f"SIGNS GREEN ({len(CASES)} spellings)")
