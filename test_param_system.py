# -*- coding: utf-8 -*-
"""
Stand for MATRIX-DESIGN.md: linear systems with parameters in the coefficients.

Every expected range below is computed by a DIFFERENT formulation than the one
the solver reads — circuits by nodal analysis over exact fractions at every
corner of the parameter box, not by the Ohm/Kirchhoff rows the sheet carries —
so agreement is not the solver agreeing with itself.

Checks:
  1. series pair, divider, Wheatstone bridge (all parts boxed): every unknown's
     box equals the corner hull of the nodal solution, exactly;
  2. random small networks (seeded): zero mismatches;
  3. OUTSIDE the class — a parameter with rank two in the coefficients, whose
     true range has an interior extreme (x = p/(1+p^2), peak at p = 1): NOT
     narrowed, and the log names the reason; the claim x <= 9/20 is not T;
  4. nothing changes where the floor already worked: a box only on the right
     (x + y == 10) takes the old path, same log line; constant systems too;
  5. overdetermined systems are refused, singular ones are refused;
  6. MUTATION: with the rank test forced to say "exact", check 3 must FAIL —
     the stand catches a broken guard.

Run:  python3 test_param_system.py     -> PARAM SYSTEM GREEN
"""
import itertools
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import znumsolve                                           # noqa: E402
from znumjudge import parse_quantities                    # noqa: E402
from znumsolve import solve_claim                          # noqa: E402

ok = fail = 0


def check(name, cond, extra=""):
    global ok, fail
    if cond:
        ok += 1
        print(f"  ok   {name}")
    else:
        fail += 1
        print(f"  FAIL {name} {extra}")


# ------------------------------------------------- an independent oracle
def nodal(n, edges, src, R, V):
    """Branch currents and node voltages by nodal analysis (exact)."""
    a, b = edges[src]
    free = [x for x in range(n) if x not in (a, b)]
    idx = {x: i for i, x in enumerate(free)}
    m = len(free)
    A = [[F(0)] * m for _ in range(m)]
    rhs = [F(0)] * m
    for i, (u, v) in enumerate(edges):
        if i == src:
            continue
        g = 1 / R[i]
        for p, q in ((u, v), (v, u)):
            if p in idx:
                A[idx[p]][idx[p]] += g
                if q in idx:
                    A[idx[p]][idx[q]] -= g
                elif q == a:
                    rhs[idx[p]] += g * V
    for c in range(m):
        piv = next(r for r in range(c, m) if A[r][c] != 0)
        A[c], A[piv] = A[piv], A[c]
        rhs[c], rhs[piv] = rhs[piv], rhs[c]
        for r in range(m):
            if r != c and A[r][c] != 0:
                f = A[r][c] / A[c][c]
                A[r] = [x - f * y for x, y in zip(A[r], A[c])]
                rhs[r] -= f * rhs[c]
    volt = {a: V, b: F(0)}
    for x in free:
        volt[x] = rhs[idx[x]] / A[idx[x]][idx[x]]
    cur = {i: (volt[u] - volt[v]) / R[i] for i, (u, v) in enumerate(edges) if i != src}
    return cur, volt


def sheet(n, edges, src, boxes, V):
    """The studio-style sheet: parts as boxes, unknowns '?', local laws."""
    a, b = edges[src]
    nm = lambda x: "V" if x == a else ("0" if x == b else f"U{x}")
    q = [f"V={V} earned:psu"] + [f"R{i}=[{lo},{hi}] credit" for i, (lo, hi) in boxes.items()]
    q += [f"U{x}=? credit" for x in range(n) if x not in (a, b)]
    q += [f"I{i}=? credit" for i in boxes]
    laws = [f"({nm(u)} - {nm(v)} == I{i}*R{i})" for i, (u, v) in enumerate(edges) if i != src]
    for x in range(n):
        if x in (a, b):
            continue
        ins = [f"I{i}" for i, (u, v) in enumerate(edges) if i != src and v == x and u != x]
        outs = [f"I{i}" for i, (u, v) in enumerate(edges) if i != src and u == x and v != x]
        laws.append(f"({' + '.join(ins) or '0'} == {' + '.join(outs) or '0'})")
    return ", ".join(q), " & ".join(laws)


def compare(n, edges, src, boxes, V, label):
    qt, claim = sheet(n, edges, src, boxes, V)
    r = solve_claim(claim, *parse_quantities(qt))
    nar = r["narrowed"]
    res = sorted(boxes)
    lo = {i: None for i in res}; hi = {i: None for i in res}
    for corner in itertools.product(*[boxes[i] for i in res]):
        R = {i: F(c) for i, c in zip(res, corner)}
        R[src] = F(1)
        cur, _ = nodal(n, edges, src, [R.get(i, F(1)) for i in range(len(edges))], F(V))
        for i in res:
            lo[i] = cur[i] if lo[i] is None or cur[i] < lo[i] else lo[i]
            hi[i] = cur[i] if hi[i] is None or cur[i] > hi[i] else hi[i]
    bad = [i for i in res if (nar[f"I{i}"]["lo"], nar[f"I{i}"]["hi"]) != (lo[i], hi[i])]
    check(label, not bad, f"mismatched currents {bad}; log {r['log'][:2]}")


def main():
    print("1. circuits against nodal analysis at every corner")
    compare(3, [(0, 2), (0, 1), (1, 2)], 0, {1: (90, 110), 2: (90, 110)}, 10, "series pair")
    compare(3, [(0, 2), (0, 1), (1, 2), (1, 2)], 0, {1: (90, 110), 2: (180, 220), 3: (45, 55)}, 12,
            "divider with a parallel pair")
    compare(4, [(0, 3), (0, 1), (0, 2), (1, 3), (2, 3), (1, 2)], 0,
            {1: (90, 110), 2: (180, 220), 3: (90, 110), 4: (135, 165), 5: (70, 85)}, 10,
            "Wheatstone bridge, every part boxed")

    print("2. random small networks (seeded)")
    rnd = random.Random(20261009)
    mism = ran = 0
    for t in range(40):
        n = rnd.randint(3, 5)
        edges = [(0, n - 1)]
        for x in range(1, n):                              # a spanning path keeps it connected
            edges.append((x - 1, x))
        for _ in range(rnd.randint(1, 4)):
            u, v = rnd.sample(range(n), 2)
            edges.append((u, v))
        boxes = {}
        for i in range(1, len(edges)):
            if rnd.random() < 0.6 and len(boxes) < 6:
                c = rnd.choice([47, 68, 100, 150, 220])
                boxes[i] = (F(c) * F(9, 10), F(c) * F(11, 10))
            else:
                c = F(rnd.choice([47, 68, 100, 150, 220]))
                boxes[i] = (c, c)
        if all(lo == hi for lo, hi in boxes.values()):
            continue
        qt, claim = sheet(n, edges, 0, boxes, 10)
        r = solve_claim(claim, *parse_quantities(qt))
        nar = r["narrowed"]
        res = sorted(boxes)
        lo = {i: None for i in res}; hi = {i: None for i in res}
        for corner in itertools.product(*[sorted({boxes[i][0], boxes[i][1]}) for i in res]):
            R = [F(1)] * len(edges)
            for i, c in zip(res, corner):
                R[i] = F(c)
            try:
                cur, _ = nodal(n, edges, 0, R, F(10))
            except StopIteration:
                break
            for i in res:
                lo[i] = cur[i] if lo[i] is None or cur[i] < lo[i] else lo[i]
                hi[i] = cur[i] if hi[i] is None or cur[i] > hi[i] else hi[i]
        else:
            ran += 1
            for i in res:
                if (nar[f"I{i}"]["lo"], nar[f"I{i}"]["hi"]) != (lo[i], hi[i]):
                    mism += 1
                    break
    check(f"{ran} seeded networks (of 40 drawn): every current equals the corner hull",
          mism == 0 and ran >= 30, f"{mism} mismatched, {ran} ran")

    print("3. outside the class: rank two, interior extreme")
    out_of_class()

    print("4. nothing changes where the floor already worked")
    r = solve_claim("(x + y == 10) & (x <= 9)", *parse_quantities("y=[1,2] credit, x=? credit"))
    check("box only on the right takes the old path, same log line",
          r["log"] == ["x -> [8, 9] by [x + y == 10]"], str(r["log"]))
    r = solve_claim("(x + y == 10) & (x - y == 2)", *parse_quantities("x=? credit, y=? credit"))
    check("constant system: exact elimination as before",
          any("by exact elimination" in l for l in r["log"]) and r["narrowed"]["x"]["lo"] == 6)

    print("5. refused shapes")
    r = solve_claim("(x*p == 1) & (x*q == 1)",
                    *parse_quantities("p=[1,2] credit, q=[1,2] credit, x=? credit"))
    check("overdetermined: refused, named", any("overdetermined" in l for l in r["log"]), str(r["log"]))
    r = solve_claim("(x*p - y == 0) & (x - y == 1)",
                    *parse_quantities("p=[1/2,2] credit, x=? credit, y=? credit"))
    check("singular inside the box (det = p - 1 changes sign): refused, named",
          any("changes sign" in l or "singular" in l for l in r["log"]), str(r["log"]))

    r = solve_claim("(V - U == I*R1) & (U == I*R2) & (I*I == I*I)",
                    *parse_quantities("V=10 earned:s, R1=[90,110] credit, R2=[180,220] credit, "
                                      "I=? credit, U=? credit"))
    check("a row not linear in the unknowns: the range is kept but NOT called exact",
          any("over the linear rows only" in l for l in r["log"])
          and not any("exact at the corners" in l for l in r["log"]), str(r["log"]))

    print("7. stage two: dependence, and no self-fulfilling verdict")
    def disp(sheet_, claim):
        r = solve_claim(claim, *parse_quantities(sheet_))
        return r["disposition"], r.get("polarity")
    y = "y=[1,2] earned:d, x=? credit"
    check("(y >= 3/2) & (x == 1), y measured in [1,2]: NOT earned (was EARNED, live)",
          disp(y, "(y >= 3/2) & (x == 1)")[0] == "OPEN")
    check("x + y == 10 alone: EARNED (x = 10 - y at every reading)", disp(y, "x + y == 10")[0] == "EARNED")
    check("(x + y == 10) & (x <= 9): EARNED", disp(y, "(x + y == 10) & (x <= 9)")[0] == "EARNED")
    check("(x + y == 10) & (x <= 17/2): OPEN (x = 9 at y = 1; the narrowed y must not decide it)",
          disp(y, "(x + y == 10) & (x <= 17/2)")[0] == "OPEN")
    check("(x + y == 10) & (x >= 11): REFUTED", disp(y, "(x + y == 10) & (x >= 11)")[0] == "REFUTED")
    circ = "V=10 earned:p, R1=[90,110] earned:d1, R2=[180,220] {p2}, I=? credit, U=? credit"
    check("circuit, all datasheets: laws & I <= 1/20 EARNED",
          disp(circ.format(p2="earned:d2"), "(V - U == I*R1) & (U == I*R2) & (I <= 1/20)")[0] == "EARNED")
    check("circuit, R2 on credit: ON CREDIT toward T",
          disp(circ.format(p2="credit"), "(V - U == I*R1) & (U == I*R2) & (I <= 1/20)")
          == ("ON CREDIT", "toward T"))
    check("circuit: I <= 1/30 with I in [1/33, 1/27]: OPEN",
          disp(circ.format(p2="earned:d2"), "(V - U == I*R1) & (U == I*R2) & (I <= 1/30)")[0] == "OPEN")
    check("an interval literal (x == [3,4]) is membership, not a parameter: OPEN as before",
          disp("x=? credit", "x == [3,4]")[0] == "OPEN")
    saved_l = znumsolve._verdict_ledger
    znumsolve._verdict_ledger = lambda qs, quantities: qs
    caught = disp(y, "(y >= 3/2) & (x == 1)")[0] == "EARNED"
    znumsolve._verdict_ledger = saved_l
    check("mutation: judging on the narrowed ledger again brings the self-fulfilling EARNED back",
          caught)

    print("8. stage two on random networks: the verdict on a current's bound vs nodal corners")
    rnd2 = random.Random(9102026)
    agree = total = 0
    for t in range(60):
        n = rnd2.randint(3, 5)
        edges = [(0, n - 1)] + [(x - 1, x) for x in range(1, n)]
        for _ in range(rnd2.randint(1, 3)):
            u, v = rnd2.sample(range(n), 2)
            edges.append((u, v))
        boxes = {i: (F(c) * F(9, 10), F(c) * F(11, 10))
                 for i in range(1, len(edges)) for c in [rnd2.choice([47, 100, 220])]}
        if len(boxes) > 8:
            continue
        res = sorted(boxes)
        k = rnd2.choice(res)
        vals = []
        for corner in itertools.product(*[boxes[i] for i in res]):
            R = [F(1)] * len(edges)
            for i, c in zip(res, corner):
                R[i] = c
            cur, _ = nodal(n, edges, 0, R, F(10))
            vals.append(cur[k])
        c = rnd2.choice([min(vals) - F(1, 1000), max(vals) + F(1, 1000), (min(vals) + max(vals)) / 2])
        want = (("ON CREDIT", "toward T") if max(vals) <= c else
                ("ON CREDIT", "toward F") if min(vals) > c else ("OPEN", None))
        qt, claim = sheet(n, edges, 0, boxes, 10)
        r = solve_claim(claim + f" & (I{k} <= {c})", *parse_quantities(qt))
        total += 1
        agree += (r["disposition"], r.get("polarity")) == want
    check(f"{agree} of {total} random bounds judged as the corners say (credit parts)",
          agree == total and total >= 40, f"{agree}/{total}")

    print("6. mutation: a guard that always says 'exact' must turn check 3 red")
    saved = znumsolve._rank_one_in
    znumsolve._rank_one_in = lambda *a, **k: True
    global ok, fail
    before = fail
    quiet_ok, quiet_fail = ok, fail
    caught = not out_of_class(quiet=True)
    ok, fail = quiet_ok, quiet_fail
    znumsolve._rank_one_in = saved
    check("mutation caught (the out-of-class check fails under the broken guard)", caught)

    print(f"\n{ok} ok, {fail} fail")
    if fail == 0:
        print("PARAM SYSTEM GREEN")
    return 0 if fail == 0 else 1


def out_of_class(quiet=False):
    """x - p*y == 0, p*x + y == 1  ->  x = p/(1+p^2): peak 1/2 at p = 1, corners 2/5."""
    sheet_ = "p=[1/2,2] credit, x=? credit, y=? credit"
    r0 = solve_claim("(x - p*y == 0) & (p*x + y == 1)", *parse_quantities(sheet_))
    refused = any("rank > 1" in l for l in r0["log"])
    # the laws alone: x must not be narrowed below its true max 1/2 (the corner
    # hull would say [2/5, 2/5]); the requirement is judged in a separate claim,
    # since a committed x <= 9/20 narrows x by itself, as the floor should
    not_narrowed = r0["narrowed"]["x"]["hi"] >= F(1, 2)
    r = solve_claim("(x - p*y == 0) & (p*x + y == 1) & (x <= 9/20)", *parse_quantities(sheet_))
    not_T = r["disposition"] not in ("EARNED",) and not (r["disposition"] == "ON CREDIT"
                                                         and r.get("polarity") == "toward T")
    r = r0
    good = refused and not_narrowed and not_T
    if not quiet:
        check("rank two: refused and named", refused, str(r["log"]))
        check("rank two: x not narrowed to the wrong corner hull [2/5, 2/5]", not_narrowed,
              str(r0["narrowed"]["x"]))
        check("rank two: x <= 9/20 not certified (true max is 1/2)", not_T, r["disposition"])
    return good


if __name__ == "__main__":
    sys.exit(main())
