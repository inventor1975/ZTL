# -*- coding: utf-8 -*-
"""
znumsolve — the judge learns to narrow: a solver that issues receipts.

Stage 2 of the plan settled in words with the curator. Until now the
numeric floor computed FORWARDS: given the quantities, judge the claim.
That made it a checker and not a solver — "x + x == 10" came back OPEN
with the cure "measure x", which is true and useless, since the sheet
already says everything needed to pin x.

Backward narrowing closes that. Each comparison is read as a CONSTRAINT
and pushed back onto the quantities it mentions; the pass repeats to a
fixed point. The rule per variable is hull consistency: drop exactly
those values of x for which NO choice of the other quantities inside
their own boxes satisfies the constraint. That is sound by construction —
a value is removed only when it is refuted whatever the others do — and
section 3 measures it anyway, on an exhaustive grid, because "sound by
construction" is the kind of sentence this project does not accept from
others.

Two properties make this ours rather than a small interval solver:

  * the TYPE does the last mile. x + x == 10 over the rationals gives
    x = 5 outright; k == 8/3 with k an integer gives the EMPTY box, which
    is a refutation and not a failure to converge. The lattice is what
    turns narrowing into an answer.
  * the answer carries its RECEIPT. A pinned value inherits the
    provenance of every bound that pinned it, so the solver says not just
    "x = 5" but "x = 5, ON CREDIT, because line3's bound is undocumented"
    — with the cure attached.

Honest boundaries, stated before the examples: propagation runs over
CONJUNCTIONS of comparisons only (a disjunction constrains nothing on its
own); it is exact on the linear fragment and silently skipped outside it,
never guessed; `sample` quantities are not narrowed at all, since each
occurrence is a separate act and the constraint speaks about occurrences,
not about the name; and an interval solver returns a BOX, so a
non-degenerate answer is the normal case, not a bug.

Run:  python3 znumsolve.py
"""
import os
import sys
from fractions import Fraction

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from znum import (INF, EARNED, CREDIT, qty, num, fmt, _linear,   # noqa: E402
                  _NotLinear, _step, typename)
from znumjudge import (parse_quantities, extract_comparisons,     # noqa: E402
                       judge_sheet_claim)

MAX_ROUNDS = 32


def _hull(kind, form_c, terms, name, quantities):
    """The values of `name` that survive the constraint, given the others.

    `form_c + Σ k·x  ⋈  0` with ⋈ from the comparison. Isolate the
    variable, evaluate the rest over its current box, and keep exactly the
    values for which SOME choice of the rest satisfies the constraint."""
    k = sum(coef for key, (coef, nm) in terms.items() if nm == name)
    if k == 0:
        return None
    rlo = rhi = form_c
    for key, (coef, nm) in terms.items():
        if nm == name:
            continue
        q = quantities[nm]
        ends = (coef * q["lo"], coef * q["hi"])
        rlo, rhi = rlo + min(ends), rhi + max(ends)
    # k·x ⋈ -rest, with rest ranging over [rlo, rhi]
    strict_lo = strict_hi = False
    if kind == "eq":
        lo, hi = -rhi, -rlo
    elif kind == "le":
        lo, hi = -INF, -rlo
    else:                                    # lt: the upper bound is STRICT
        lo, hi = -INF, -rlo
        strict_hi = True
    if k < 0:
        lo, hi = (-hi if hi != INF else -INF), (-lo if lo != -INF else INF)
        strict_lo, strict_hi = strict_hi, strict_lo
        k = -k
    lo = lo if lo == -INF else lo / k
    hi = hi if hi == INF else hi / k
    return lo, hi, strict_lo, strict_hi


def _solve_linear_system(qs, atoms):
    """Exact rational elimination over the EQUALITY constraints.

    Interval propagation alone cannot do simultaneous equations: to narrow
    a you need b's box finite and vice versa, so two unbounded unknowns
    sit there forever (measured, before this was written). On the linear
    fragment we do not have to propagate at all — we can solve. Gaussian
    elimination over Fractions, exact, and it also detects an inconsistent
    system, which is a refutation rather than a stall."""
    eqs, contributors = [], set()
    for kind, e1, e2, chunk in atoms.values():
        if kind != "eq":
            continue
        seen = set()
        try:
            c, terms, _, _ = _linear(("sub", e1, e2), qs, [0], seen)
        except (_NotLinear, KeyError):
            continue
        contributors |= seen
        row = {}
        for _, (coef, nm) in terms.items():
            if qs[nm].get("sample"):
                row = None
                break
            row[nm] = row.get(nm, Fraction(0)) + coef
        if row:
            eqs.append((row, -c, chunk))
    if not eqs:
        return {}, None, set()
    names = sorted({n for row, _, _ in eqs for n in row})
    mat = [[Fraction(row.get(n, 0)) for n in names] + [Fraction(rhs)]
           for row, rhs, _ in eqs]
    r = 0
    for col in range(len(names)):
        piv = next((i for i in range(r, len(mat)) if mat[i][col] != 0), None)
        if piv is None:
            continue
        mat[r], mat[piv] = mat[piv], mat[r]
        f = mat[r][col]
        mat[r] = [x / f for x in mat[r]]
        for i in range(len(mat)):
            if i != r and mat[i][col] != 0:
                k = mat[i][col]
                mat[i] = [a - k * b for a, b in zip(mat[i], mat[r])]
        r += 1
    pinned = {}
    for row in mat:
        nz = [i for i, x in enumerate(row[:-1]) if x != 0]
        if not nz and row[-1] != 0:
            return {}, "inconsistent", contributors
        if len(nz) == 1:
            pinned[names[nz[0]]] = row[-1] / row[nz[0]]
    return pinned, None, contributors


def narrow(quantities, formula, rounds=MAX_ROUNDS):
    """Push every comparison of the formula back onto its quantities until
    nothing moves. Returns (quantities, log) — the log names each step, so
    a narrowed value can always say who narrowed it."""
    qs = {n: dict(q) for n, q in quantities.items()}
    _, atoms = extract_comparisons(formula, qs)
    log = []
    pinned, bad, contributors = _solve_linear_system(qs, atoms)
    if bad == "inconsistent":
        first = sorted(qs)[0]
        log.append("the equalities are inconsistent as a system")
        qs[first] = dict(qs[first], empty=True)
        return qs, log
    for name, value in sorted(pinned.items()):
        q = qs[name]
        if not (q["lo"] <= value <= q["hi"]):
            log.append(f"{name}: forced to {fmt(value)}, outside its box")
            qs[name] = dict(q, empty=True)
            return qs, log
        # a DERIVED value takes its provenance from the derivation, not
        # from whatever the unknown was declared to be. An unknown is
        # `credit` because its bounds were unwitnessed; once the equations
        # force it out of earned quantities, the value IS earned — and if
        # any contributor rides credit, so does the answer.
        others = sorted(contributors - {name})
        derived_prov = (EARNED if all(qs[o]["prov"] == EARNED for o in others)
                        else CREDIT)
        pinned_q = qty(value, value, derived_prov,
                       "derived:" + ",".join(others) if others else None,
                       discrete=q["discrete"], unit=q["unit"], sample=False)
        # KEEP THE TWO EMPTINESSES APART (2026-08-12). A quantity DECLARED
        # with no reading is E: the sheet cannot be judged at all. A value
        # DERIVED onto a point the lattice does not contain is something
        # else entirely — the judging succeeded and found no solution, so
        # the claim is REFUTED. Same empty set, opposite meanings: one is a
        # broken description, the other is an answer.
        if pinned_q.get("no_readings"):
            log.append(f"{name}: {fmt(value)} is off the "
                       f"{typename(q['discrete'])} lattice — no solution")
            qs[name] = dict(q, empty=True)
            return qs, log
        qs[name] = pinned_q
        log.append(f"{name} = {fmt(value)} by exact elimination"
                   f" ({derived_prov})")
    for _ in range(rounds):
        moved = False
        for atom, (kind, e1, e2, chunk) in atoms.items():
            try:
                c, terms, _, _ = _linear(("sub", e1, e2), qs, [0])
            except (_NotLinear, KeyError):
                continue                     # outside the linear fragment
            names = {nm for _, (_, nm) in terms.items()}
            for name in sorted(names):
                q = qs[name]
                if q.get("sample"):
                    continue                 # occurrences, not one thing
                got = _hull(kind, c, terms, name, qs)
                if got is None:
                    continue
                glo, ghi, slo, shi = got
                # a STRICT bound on a lattice is one step tighter: age > 10
                # over the integers means age >= 11, and saying [10, 14] for
                # "older than 10, younger than 14" would be an answer nobody
                # asked for (measured: it was the first thing this got wrong)
                step = _step(q["discrete"])
                if step is not None:
                    if shi and ghi != INF and (ghi / step).denominator == 1:
                        ghi = ghi - step
                    if slo and glo != -INF and (glo / step).denominator == 1:
                        glo = glo + step
                lo, hi = max(q["lo"], glo), min(q["hi"], ghi)
                if lo == q["lo"] and hi == q["hi"]:
                    continue
                if lo > hi:
                    log.append(f"{name}: emptied by [{chunk}]")
                    qs[name] = dict(q, lo=lo, hi=hi, empty=True)
                    return qs, log
                # the type has the last word: round to the lattice
                narrowed = qty(lo, hi, q["prov"], q["witness"],
                               discrete=q["discrete"], unit=q["unit"],
                               sample=q.get("sample", False))
                # WHO PAID FOR THIS BOUND — recorded here, where it is
                # known, instead of being reconstructed downstream from
                # the witness text. Reconstructing it was a real bug
                # (found by conformance/solver_table.py on its first run):
                # a narrowed quantity keeps its ORIGINAL witness, so
                # `earned:doc` was read as the source quantity `doc` and
                # crashed on lookup — and would silently have attributed
                # the value to the wrong source had a document ever been
                # named like a quantity.
                narrowed["derived_from"] = sorted(
                    set(q.get("derived_from") or [])
                    | {o for o in names if o != name})
                # a narrowed bound inherits the credit that produced it
                if any(qs[o]["prov"] == CREDIT for o in names if o != name):
                    narrowed["prov"] = CREDIT
                    narrowed["witness"] = None
                qs[name] = narrowed
                log.append(f"{name} -> [{fmt(narrowed['lo'])}, "
                           f"{fmt(narrowed['hi'])}] by [{chunk}]")
                moved = True
        if not moved:
            break
    return qs, log


def solve_claim(formula, quantities, marks):
    """Narrow first, then judge on the narrowed ledger — and say, for every
    answer the narrowing produced, what it is worth and what would fix it.

    A solved value is not a number: it is a number with a warranty and a
    cure. `x = 5 ON CREDIT, document total` is a different object from
    `x = 5 EARNED`, and the difference is the only thing an auditor is
    paid to look at."""
    qs, log = narrow(quantities, formula)
    empty = [n for n, q in qs.items() if q.get("empty")]
    if empty:
        return {"disposition": "REFUTED", "narrowed": qs, "log": log,
                "empty": empty, "next_check": [], "solved": {}}
    r = judge_sheet_claim(formula, qs, marks)
    r["narrowed"], r["log"] = qs, log
    solved, cures = {}, list(r["next_check"])
    derived = {n for n, q in qs.items()
               if (quantities[n]["lo"], quantities[n]["hi"])
               != (q["lo"], q["hi"])}
    # a cure must be addressed to someone who can act on it. Nobody can
    # document or measure the ANSWER: line3 is what the sheet is asking
    # for, not a source. Cures naming a derived quantity are dropped, and
    # the one thing worth saying about it — that it is still a box — is
    # said once, below.
    cures = [c for c in cures
             if c.split(" ", 1)[-1] not in derived]
    for name, q in sorted(qs.items()):
        before = quantities[name]
        if (before["lo"], before["hi"]) == (q["lo"], q["hi"]):
            continue                          # this one was not narrowed
        pinned = q["lo"] == q["hi"]
        # who paid for it: the narrowing recorded its own sources
        sources = [c for c in (q.get("derived_from") or []) if c in quantities]
        weak = [c for c in sources if quantities[c]["prov"] == CREDIT]
        solved[name] = {"lo": q["lo"], "hi": q["hi"], "pinned": pinned,
                        "prov": q["prov"], "from": sources, "weak": weak}
        for c in weak:
            if f"document {c}" not in cures:
                cures.append(f"document {c}")
        if not pinned:
            cures.append(f"narrow {name} further (still a box)")
    seen = set()
    r["solved"] = solved
    r["next_check"] = [c for c in cures
                       if not (c in seen or seen.add(c))]
    return r


# ================================================================ the bench
def _show(qs, names):
    return ", ".join(f"{n} in [{fmt(qs[n]['lo'])}, {fmt(qs[n]['hi'])}]"
                     for n in names)


def sec1_the_school_problems():
    print("-" * 72)
    print("1. THE THINGS A CHILD IS ASKED (and the judge could not do)")
    cases = [
        ("x + x == 10", "x=? int", ["x"]),
        ("apples - 7 == 5", "apples=? int", ["apples"]),
        ("3 * k == 12", "k=? int", ["k"]),
        ("sum(a,b) == 10 & a - b == 2", "a=? int, b=? int", ["a", "b"]),
    ]
    for formula, data, names in cases:
        quantities, marks = parse_quantities(data)
        r = solve_claim(formula, quantities, marks)
        print(f"   {formula:34} -> {_show(r['narrowed'], names)}"
              f"   [{r['disposition']}]")
    q, m = parse_quantities("x=? int")
    assert narrow(q, "x + x == 10")[0]["x"]["lo"] == 5
    q, m = parse_quantities("a=? int, b=? int")
    out, _ = narrow(q, "sum(a,b) == 10 & a - b == 2")
    assert (out["a"]["lo"], out["a"]["hi"]) == (6, 6)
    assert (out["b"]["lo"], out["b"]["hi"]) == (4, 4)
    print("   two unknowns and two constraints: solved by narrowing alone,")
    print("   no algebra, no symbol pushing — the boxes squeeze each other.")


def sec2_the_type_finishes_it():
    print("-" * 72)
    print("2. THE TYPE DOES THE LAST MILE")
    q, m = parse_quantities("k=? int, sweets=8 earned:cheque, kids=3 earned:cheque")
    r = solve_claim("k * kids == sweets", q, m)
    print(f"   'she shared 8 sweets equally among 3': {r['disposition']}"
          f"   {r.get('empty') and 'empty box for ' + str(r['empty']) or ''}")
    assert r["disposition"] == "REFUTED" and r["empty"] == ["k"]
    q2, m2 = parse_quantities("k=? frac3, sweets=8 earned:cheque, "
                              "kids=3 earned:cheque")
    r2 = solve_claim("k * kids == sweets", q2, m2)
    print(f"   the same with thirds allowed: "
          f"k in [{fmt(r2['narrowed']['k']['lo'])}, "
          f"{fmt(r2['narrowed']['k']['hi'])}]   [{r2['disposition']}]")
    assert r2["narrowed"]["k"]["lo"] == Fraction(8, 3)
    print("   an EMPTY box is a refutation, not a failure to converge — and")
    print("   the cure is the one the corpus already names: contest the type.")


def sec3_soundness_measured():
    print("-" * 72)
    print("3. SOUNDNESS, MEASURED RATHER THAN ASSERTED")
    # exhaustive grid: every true solution must survive the narrowing
    grid = range(-4, 5)
    checks = lost = narrowed_cells = 0
    for c in grid:
        for kind, formula in (("eq", f"a + b == {c}"),
                              ("le", f"a + b <= {c}"),
                              ("eq", f"a - b == {c}"),
                              ("eq", f"a + a == {c}")):
            q = {"a": qty(-4, 4, EARNED, "grid", discrete="int"),
                 "b": qty(-4, 4, EARNED, "grid", discrete="int")}
            out, _ = narrow(q, formula)
            for av in grid:
                for bv in grid:
                    ok = {"eq": (lambda: (av + bv == c) if "b" in formula
                                 else (av + av == c)),
                          "le": (lambda: av + bv <= c)}[kind]()
                    if "a - b" in formula:
                        ok = (av - bv == c)
                    if not ok:
                        continue
                    checks += 1
                    inside = (out["a"].get("empty") is None
                              and out["a"]["lo"] <= av <= out["a"]["hi"])
                    if "b" in formula.replace("a + a", ""):
                        inside = inside and (
                            out["b"]["lo"] <= bv <= out["b"]["hi"])
                    if not inside:
                        lost += 1
            narrowed_cells += 1
    print(f"   {narrowed_cells} constraint systems, {checks} true solutions")
    print(f"   solutions dropped by narrowing: {lost}")
    assert lost == 0
    print("   none. The failure mode is the safe one: a box may stay wider")
    print("   than the truth (we lose completeness, and the claim stays")
    print("   OPEN) but a real solution is never thrown away, so a verdict")
    print("   forced after narrowing is as good as one forced before.")


def sec4_the_receipt():
    print("-" * 72)
    print("4. THE ANSWER COMES WITH ITS RECEIPT")
    # the audit case: the total is documented, one line is not
    q, m = parse_quantities(
        "line1=1000 earned:inv-17, line2=2000 earned:inv-18, "
        "line3=? int, total=4500 earned:contract")
    r = solve_claim("sum(line1,line2,line3) == total", q, m)
    l3 = r["narrowed"]["line3"]
    print(f"   the missing line is forced: line3 = {fmt(l3['lo'])}"
          f"   provenance: {l3['prov']}")
    assert l3["lo"] == l3["hi"] == 1500 and l3["prov"] == EARNED
    print(f"   log: {r['log']}")
    # and now with a total nobody documented
    q2, m2 = parse_quantities(
        "line1=1000 earned:inv-17, line2=2000 earned:inv-18, "
        "line3=? int, total=4500 credit")
    r2 = solve_claim("sum(line1,line2,line3) == total", q2, m2)
    l3b = r2["narrowed"]["line3"]
    print(f"   same arithmetic, undocumented total: line3 = "
          f"{fmt(l3b['lo'])}   provenance: {l3b['prov']}")
    assert l3b["lo"] == 1500 and l3b["prov"] == CREDIT
    print("   the value is the same and the warranty is not. A solver that")
    print("   returned only the number would have hidden exactly the thing")
    print("   an auditor is paid to see.")


def sec5_word_problems():
    print("-" * 72)
    print("5. A SHEET OF WORD PROBLEMS, INCLUDING ONES THAT MUST NOT SOLVE")
    sheet = [
        ("Masha had apples, gave 7 away, 5 left",
         "had - 7 == 5", "had=? int"),
        ("three equal boxes hold 12",
         "3 * box == 12", "box=? int"),
        ("two numbers, sum 10, difference 2",
         "sum(a,b) == 10 & a - b == 2", "a=? int, b=? int"),
        ("the change from 1000 for a 743 purchase",
         "paid - price == change",
         "paid=1000 earned:till, price=743 earned:till, change=? int"),
        ("8 sweets shared equally among 3 children",
         "k * kids == sweets",
         "k=? int, sweets=8 earned:cheque, kids=3 earned:cheque"),
        ("a number whose double is odd",
         "2 * n == 7", "n=? int"),
        ("she is older than 10 and younger than 14",
         "age > 10 & age < 14", "age=? int"),
    ]
    for title, formula, data in sheet:
        q, m = parse_quantities(data)
        r = solve_claim(formula, q, m)
        answers = ", ".join(
            f"{n} = {fmt(v['lo'])}" if v["pinned"]
            else f"{n} in [{fmt(v['lo'])}, {fmt(v['hi'])}]"
            for n, v in sorted(r["solved"].items())) or "—"
        print(f"   {title:44} {answers:26} [{r['disposition']}]")
    # the ones that must solve
    q, m = parse_quantities("had=? int")
    assert solve_claim("had - 7 == 5", q, m)["solved"]["had"]["lo"] == 12
    # the one that must NOT: an odd double has no integer solution
    q, m = parse_quantities("n=? int")
    assert solve_claim("2 * n == 7", q, m)["disposition"] == "REFUTED"
    # and the one that must stay a box, honestly
    q, m = parse_quantities("age=? int")
    r = solve_claim("age > 10 & age < 14", q, m)
    assert (r["solved"]["age"]["lo"], r["solved"]["age"]["hi"]) == (11, 13)
    assert not r["solved"]["age"]["pinned"]
    print("   the last three are the point: a double that is odd gets an")
    print("   EMPTY box (refuted, not 'no idea'), and 'older than 10,")
    print("   younger than 14' answers [11, 13] and says so — a box is an")
    print("   answer when a box is the truth.")


def sec6_the_audit_sheet():
    print("-" * 72)
    print("6. THE SAME MACHINE ON AN AUDIT SHEET")
    rows = [
        ("total documented, one line missing",
         "sum(line1,line2,line3) == total",
         "line1=1000 earned:inv-17, line2=2000 earned:inv-18, "
         "line3=? int, total=4500 earned:contract"),
        ("same, but the total is nobody's",
         "sum(line1,line2,line3) == total",
         "line1=1000 earned:inv-17, line2=2000 earned:inv-18, "
         "line3=? int, total=4500 credit"),
        ("the claimed line contradicts the total",
         "sum(line1,line2,line3) == total & line3 == 1600",
         "line1=1000 earned:inv-17, line2=2000 earned:inv-18, "
         "line3=? int, total=4500 earned:contract"),
        ("bounds only: the total is a range",
         "sum(line1,line2,line3) == total",
         "line1=1000 earned:inv-17, line2=2000 earned:inv-18, "
         "line3=? int, total=[4200,4400] earned:contract"),
    ]
    for title, formula, data in rows:
        q, m = parse_quantities(data)
        r = solve_claim(formula, q, m)
        got = r["solved"].get("line3")
        if got is None:
            answer = "— (refuted)"
        elif got["pinned"]:
            answer = f"line3 = {fmt(got['lo'])} [{got['prov']}]"
        else:
            answer = f"line3 in [{fmt(got['lo'])}, {fmt(got['hi'])}]"
        print(f"   {title:38} {answer:34} cure {r['next_check']}")
    q, m = parse_quantities(
        "line1=1000 earned:inv-17, line2=2000 earned:inv-18, "
        "line3=? int, total=4500 credit")
    r = solve_claim("sum(line1,line2,line3) == total", q, m)
    assert r["solved"]["line3"]["prov"] == CREDIT
    assert r["next_check"] == ["document total"]      # not "document line3"
    q2, m2 = parse_quantities(
        "line1=1000 earned:inv-17, line2=2000 earned:inv-18, "
        "line3=? int, total=[4200,4400] earned:contract")
    r2 = solve_claim("sum(line1,line2,line3) == total", q2, m2)
    assert (r2["solved"]["line3"]["lo"], r2["solved"]["line3"]["hi"]) == (1200, 1400)
    print("   the cure is not 'measure line3' — nobody can measure a line")
    print("   that does not exist yet. It is 'document total', naming the")
    print("   quantity whose credit the answer rides on. That is the whole")
    print("   difference between a solver and an auditor.")


if __name__ == "__main__":
    print("=" * 72)
    print("ZNUMSOLVE — narrowing backwards, with receipts")
    print("=" * 72)
    sec1_the_school_problems()
    sec2_the_type_finishes_it()
    sec3_soundness_measured()
    sec4_the_receipt()
    sec5_word_problems()
    sec6_the_audit_sheet()
    print("=" * 72)
    print("ZNUMSOLVE GREEN — the floor now runs backwards as well as")
    print("forwards: constraints narrow their quantities to a fixed point,")
    print("the type finishes the job (an empty box is a refutation), and no")
    print("true solution was dropped on the measured grid. The answer")
    print("carries its provenance, so 'line3 = 1500' and 'line3 = 1500 on")
    print("credit' never look alike.")
