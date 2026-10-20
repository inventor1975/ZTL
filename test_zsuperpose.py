"""Superposition (2026-10-20): a linear system with a constant matrix and a right-hand side affine in its uncertain
quantities is read exactly for ANY number of them — one elimination with 1 + #p right-hand sides
(znumsolve._superpose; lean/ZSuperpose.lean). Known answers, the old corner cap of 10 passed, the ranges compared
with brute force over every corner, and the cases that must NOT take this path.
"""
import itertools
import random
import sys
import time
from fractions import Fraction as F

from znumjudge import parse_quantities, judge_sheet_claim
from znumsolve import solve_claim, affine_range

FAILS = []
COUNT = [0]


def check(cond, what):
    COUNT[0] += 1
    print(("  ok   " if cond else "  FAIL ") + what)
    if not cond:
        FAILS.append(what)


def narrowed(claim, sheet):
    r = solve_claim(claim, parse_quantities(sheet)[0], {})
    return {k: (F(v["lo"]), F(v["hi"])) for k, v in r["narrowed"].items()}, r.get("log") or []


print("1. two equations, two parameters: x = (p+q)/2, y = (p-q)/2")
n, _ = narrowed("(x + y == p) & (x - y == q)", "p=[2,4] credit, q=[0,2] credit, x=? credit, y=? credit")
check(n["x"] == (1, 3) and n["y"] == (0, 2), f"x {n['x']}, y {n['y']}")

print("2. a chain of 12 parameters (the old corner cap was 10)")
k = 12
sheet = ", ".join([f"p{i}=[1,3] credit" for i in range(1, k + 1)] + [f"x{i}=? credit" for i in range(1, k + 1)])
claim = " & ".join(["(x1 == p1)"] + [f"(x{i} - x{i - 1} == p{i})" for i in range(2, k + 1)])
t = time.time()
n, log = narrowed(claim, sheet)
dt = time.time() - t
check(n["x12"] == (12, 36) and n["x5"] == (5, 15), f"x12 {n['x12']}, x5 {n['x5']} in {dt:.2f} s")
check(any(l.startswith("x12 -> ") and "exact" in l for l in log), "logged exact")

print("3. random dense systems: superposition against every corner (brute force)")
random.seed(20261020)
for trial in range(6):
    m, np_ = 4, 5
    while True:
        A = [[F(random.randint(-4, 4)) for _ in range(m)] for _ in range(m)]
        # det != 0 by a quick exact elimination
        M = [r[:] for r in A]
        ok = True
        for c in range(m):
            piv = next((i for i in range(c, m) if M[i][c] != 0), None)
            if piv is None:
                ok = False
                break
            M[c], M[piv] = M[piv], M[c]
            for i in range(c + 1, m):
                f = M[i][c] / M[c][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[c])]
        if ok:
            break
    B = [[F(random.randint(-3, 3)) for _ in range(np_ + 1)] for _ in range(m)]   # b0 and one column per p
    box = {f"p{j}": (F(random.randint(-2, 0)), F(random.randint(1, 3))) for j in range(np_)}
    rows = []
    for i in range(m):
        lhs = " + ".join(f"({A[i][c]})*x{c}" for c in range(m))
        rhs = " + ".join([f"({B[i][0]})"] + [f"({B[i][j + 1]})*p{j}" for j in range(np_)])
        rows.append(f"({lhs} == {rhs})")
    sheet = ", ".join([f"p{j}=[{box[f'p{j}'][0]},{box[f'p{j}'][1]}] credit" for j in range(np_)] +
                      [f"x{c}=? credit" for c in range(m)])
    n, _ = narrowed(" & ".join(rows), sheet)

    def solve(at):
        Mb = [A[i][:] + [B[i][0] + sum(B[i][j + 1] * at[f"p{j}"] for j in range(np_))] for i in range(m)]
        for c in range(m):
            piv = next(i for i in range(c, m) if Mb[i][c] != 0)
            Mb[c], Mb[piv] = Mb[piv], Mb[c]
            for i in range(m):
                if i != c and Mb[i][c] != 0:
                    f = Mb[i][c] / Mb[c][c]
                    Mb[i] = [a - f * b for a, b in zip(Mb[i], Mb[c])]
        return [Mb[i][m] / Mb[i][i] for i in range(m)]
    sols = [solve(dict(zip(box, corner))) for corner in itertools.product(*box.values())]
    want = {f"x{c}": (min(s[c] for s in sols), max(s[c] for s in sols)) for c in range(m)}
    check(all(n.get(u) == want[u] for u in want), f"trial {trial}: every range equals the corners' hull exactly")

print("4. affine_range: each term at the end its sign picks")
check(affine_range(F(1), {"a": F(2), "b": F(-3)}, {"a": (F(0), F(1)), "b": (F(-1), F(2))}) == (F(-5), F(6)),
      "1 + 2a - 3b over a in [0,1], b in [-1,2] is [-5, 6]")

print("5. what must NOT take this path")
n, log = narrowed("(k*x == p)", "k=[1,2] credit, p=[1,1] credit, x=? credit")
check(not any("superpos" in l for l in log), "a parameter in the matrix (k*x) is not superposition")
n, _ = narrowed("(x + y == p*q) & (x - y == 0)", "p=[1,2] credit, q=[1,2] credit, x=? credit, y=? credit")
check(n["x"] == (F(1, 2), 2), f"a product of parameters on the right (p*q) is read by the corners as before: x {n['x']}")

print("6. the verdict through solve_claim: 12 earned loads, a chain sum in [12, 36]")
sheet_e = ", ".join([f"p{i}=[1,3] earned" for i in range(1, k + 1)] + [f"x{i}=? credit" for i in range(1, k + 1)])
for c, want in (("x12 <= 36", "EARNED"), ("x12 <= 35", "OPEN"), ("x12 > 36", "REFUTED"), ("x12 >= 12", "EARNED")):
    got = solve_claim(claim + f" & ({c})", parse_quantities(sheet_e)[0], {})["disposition"]
    check(got == want, f"{c}: {got} (want {want})")

print()
if FAILS:
    print(f"ZSUPERPOSE RED: {len(FAILS)} of {COUNT[0]}")
    sys.exit(1)
print(f"ZSUPERPOSE GREEN: {COUNT[0]} checks")
