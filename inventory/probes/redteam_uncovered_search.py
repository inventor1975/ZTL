# -*- coding: utf-8 -*-
"""
The seeded search of the red team of the UNCOVERED core (2026-09-28).

    python3 inventory/probes/redteam_uncovered_search.py --seed 20260928 --only S[,S..] [--n N] [--json]

Sections (each compares the code with `redteam_uncovered_oracle`, which
imports none of the code under test):

  parse      ztljudge.formalize on text with MINIMAL parentheses (random
             trees printed by the oracle), on EVERY token string up to a
             length (accept/refuse and the tree against the oracle's layered
             grammar), `_show` round trips, and the table of places where
             the reading differs from the usual convention.
  backward   zbackward.backward / order and zfl.what_to_check against the
             brute-force minimal families; the memo against no memo.
  epoch      zfl.run's epoch floor on random documents; zexpire / ztime
             against the grades; EpochBoundary on the depth-2 pool; the
             numbers ztime.py and zexpire.py print in their docstrings.
  tableau    tableau.tableau_closes / prove against satisfiability; the
             sequent properties of zsequent (identity, weakening, cut).
  fo         quantifiers.ev_fo, tableau_fo.prove_fo, zfo.prove against the
             finite-domain semantics.

A "disagreement" is a WRONG forced answer. A refusal (an exception from
the parser, a budget, "not computed") is counted apart and is not one.
"""
import argparse
import json
import os
import random
import sys
import time
from itertools import product

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, ROOT)
sys.path.insert(0, HERE)

import redteam_uncovered_oracle as O          # noqa: E402

RESULTS = []


def rec(name, checked, bad, examples, **extra):
    RESULTS.append(dict(section=name, checked=checked, disagreements=bad,
                        examples=examples[:5], **extra))
    flag = "OK " if bad == 0 else "BAD"
    print(f"  [{flag}] {name}: checked {checked}, disagreements {bad}"
          + "".join(f", {k} {v}" for k, v in extra.items()))
    for e in examples[:3]:
        print(f"        e.g. {e}")


# ------------------------------------------------------------ generators
def rand_formula(rng, names, depth, consts=False):
    if depth == 0 or rng.random() < 0.25:
        if consts and rng.random() < 0.15:
            return rng.choice(O.CONSTS)
        return rng.choice(names)
    if rng.random() < 0.2:
        return ("not", rand_formula(rng, names, depth - 1, consts))
    return (rng.choice(O.BIN), rand_formula(rng, names, depth - 1, consts),
            rand_formula(rng, names, depth - 1, consts))


def all_formulas(names, max_nodes):
    """Every formula with at most max_nodes nodes over the names."""
    by = {1: list(names)}
    for n in range(2, max_nodes + 1):
        out = [("not", f) for f in by[n - 1]]
        for k in range(1, n - 1):
            for a in by[k]:
                for b in by[n - 1 - k]:
                    for op in O.BIN:
                        out.append((op, a, b))
        by[n] = out
    return [f for n in range(1, max_nodes + 1) for f in by[n]]


# ================================================================= parse
def s_parse(seed, n):
    import ztljudge as J
    rng = random.Random(seed)

    def code(text):
        try:
            return ("ok", J.formalize(text))
        except ValueError:
            return ("refused", None)
        except RecursionError:
            return ("refused-recursion", None)

    def orac(text):
        try:
            return ("ok", O.parse(text))
        except O.Refused:
            return ("refused", None)

    # (a) minimal parentheses, random trees, three spellings
    bad, ex, refused = 0, [], 0
    names = ["p", "q", "r", "a1", "x_y", "T", "F", "Z"]
    for i in range(n):
        phi = rand_formula(rng, names, rng.randint(1, 7))
        for text in (O.show_min(phi, "ascii"), O.show_min(phi, "unicode"),
                     O.show_min(phi, "ascii").replace("=", "<->")):
            st, got = code(text)
            if st != "ok":
                refused += 1
                bad += 1
                ex.append((text, st))
            elif got != phi:
                bad += 1
                ex.append((text, got, phi))
            if J.formalize(J._show(phi)) != phi:
                bad += 1
                ex.append(("_show round trip", phi))
    rec("parse: minimal parentheses == tree (and _show round trip)",
        3 * n, bad, ex)

    # (b) every token string up to length L over a small alphabet
    L = 6 if n < 50000 else 7
    alphabet = ["p", "q", "~", "&", "|", "->", "^", "=", "(", ")"]
    bad, ex, acc = 0, [], 0
    total = 0
    for length in range(0, L + 1):
        for toks in product(alphabet, repeat=length):
            text = " ".join(toks)
            total += 1
            a, b = code(text), orac(text)
            if a[0] == "ok":
                acc += 1
            if (a[0] == "ok") != (b[0] == "ok") or a[1] != b[1]:
                bad += 1
                ex.append((text, a, b))
    rec(f"parse: every token string of length <= {L} (accept/refuse + tree)",
        total, bad, ex, accepted=acc)

    # (c) random character soup, including every spelling and junk
    soup = ["p", "q", "r", " ", "~", "¬", "&", "∧", "|", "∨", "->", "→", "^",
            "⊕", "=", "↔", "<->", "(", ")", "<", "-", ">", "T", "E", "1", "_"]
    bad, ex = 0, []
    for i in range(n):
        text = "".join(rng.choice(soup) for _ in range(rng.randint(1, 14)))
        a, b = code(text), orac(text)
        if (a[0] == "ok") != (b[0] == "ok") or a[1] != b[1]:
            bad += 1
            ex.append((text, a, b))
    rec("parse: random character soup (accept/refuse + tree)", n, bad, ex)

    # (d) the convention table: `a OP1 b OP2 c` for every pair
    table = []
    for o1 in O.BIN:
        for o2 in O.BIN:
            sy = {"and": "&", "or": "|", "imp": "->", "xor": "^", "xnor": "="}
            text = f"a {sy[o1]} b {sy[o2]} c"
            got = J.formalize(text)
            conv = O.parse_conventional(text)
            if got != conv:
                sem = any(O.ev(got, dict(zip("abc", v))) != O.ev(conv, dict(zip("abc", v)))
                          for v in product(O.VALS, repeat=3))
                table.append((text, O.show_full(got), O.show_full(conv),
                              "value differs" if sem else "same values"))
    print("   reading vs the usual convention (¬ > ∧ > ∨ > → > ↔ = ⊕, → right):")
    for row in table:
        print("     ", *row, sep="  ")
    RESULTS.append(dict(section="parse: convention table", rows=table))

    # (e) the reading of random minimal texts vs the convention
    differ = differ_val = 0
    for i in range(n):
        phi = rand_formula(rng, ["a", "b", "c"], rng.randint(2, 5))
        text = O.show_min(phi)
        conv = O.parse_conventional(text)
        if conv != phi:
            differ += 1
            if any(O.ev(phi, dict(zip("abc", v))) != O.ev(conv, dict(zip("abc", v)))
                   for v in product(O.VALS, repeat=3)):
                differ_val += 1
    print(f"   of {n} random minimal texts, {differ} read differently from the "
          f"convention, {differ_val} with a different value on some marking")
    RESULTS.append(dict(section="parse: minimal texts vs convention",
                        checked=n, differ=differ, differ_value=differ_val))

    # (f) nesting depth: where the parser stops (a refusal, not a finding)
    for mk in (lambda k: "(" * k + "p" + ")" * k, lambda k: "~" * k + "p",
               lambda k: " -> ".join(["p"] * k)):
        lo, hi = 1, 4000
        while lo < hi:
            mid = (lo + hi) // 2
            if code(mk(mid))[0] == "ok":
                lo = mid + 1
            else:
                hi = mid
        print(f"   first refused depth for {mk(3)!r}-shape: {lo} "
              f"({len(mk(lo))} characters): {code(mk(lo))[0]}")


# ============================================================== backward
def _code_family(fam):
    return sorted((tuple(S) for S in fam), key=lambda s: (len(s), s))


def s_backward(seed, n):
    import zbackward as B
    import zfl
    import ztljudge as J
    rng = random.Random(seed)
    targets = [("EARNED", True), ("REFUTED", True), (frozenset({"EARNED", "REFUTED"}), True),
               ("ON CREDIT", True), ("OPEN", True), ("T", False), ("F", False)]
    checked = 0
    c_min = c_trunc = c_order = c_memo = c_other = 0
    ex_min, ex_trunc, ex_order, ex_memo, ex_other = [], [], [], [], []
    for i in range(n):
        k = rng.randint(1, 6)
        names = [f"a{j}" for j in range(k)]
        phi = rand_formula(rng, names, rng.randint(1, 4), consts=rng.random() < 0.2)
        marking = {a: rng.choice([O.Z, O.Z, O.T, O.F]) for a in sorted(O.atoms(phi))}
        if rng.random() < 0.1:
            marking["zz"] = O.Z                  # a foreign unverified ground
        if rng.random() < 0.1 and marking:
            marking[rng.choice(sorted(marking))] = O.E
        grounds = tuple(sorted(a for a, v in marking.items() if v == O.Z))
        if len(grounds) > 7:
            continue
        memo = {}
        for target, by_disp in targets:
            if not by_disp and O.E in marking.values():
                continue        # ztl.ev is defined on T/F/Z only (a note, not a finding)
            checked += 1
            max_k = rng.choice([4, 4, 2])
            r = B.backward(phi, dict(marking), target, by_disposition=by_disp, max_k=max_k)
            r2 = B.backward(phi, dict(marking), target, by_disposition=by_disp,
                            max_k=max_k, memo=memo if by_disp else {})
            if r != r2:
                c_memo += 1
                ex_memo.append((phi, marking, target))
            if "отказ" not in r and ("не_искал_дальше" in r) != (
                    min(len(grounds), max_k) < len(grounds)):
                c_other += 1
                ex_other.append(("truncation note", phi, marking, max_k))
            pos, gua = O.families(phi, marking, target, by_disp)
            already = () in pos
            if r["already"] != already:
                c_other += 1
                ex_other.append(("already", phi, marking, target))
                continue
            got_p, got_g = _code_family(r["possible"]), _code_family(r["guaranteed"])
            if already:
                if got_p or got_g:
                    c_min += 1
                    ex_min.append((O.show_full(phi), marking, target, got_p, got_g))
            else:
                want_p = [S for S in pos if len(S) <= max_k]
                want_g = [S for S in gua if len(S) <= max_k]
                if "отказ" not in r and (got_p != want_p or got_g != want_g):
                    c_other += 1
                    ex_other.append((O.show_full(phi), marking, target, got_p, want_p, got_g, want_g))
                if (r["possible_none"] and pos) or (r["guaranteed_none"] and gua):
                    c_trunc += 1
                    ex_trunc.append((O.show_full(phi), marking, target, "none claimed",
                                     "oracle", pos[:2], gua[:2]))
            if by_disp and max_k == 4:
                s = B.order(phi, dict(marking), target)
                wrong = (s.startswith("НЕТ НАБОРА") and pos) or \
                        (s.startswith("ГАРАНТИИ НЕТ") and gua)
                if wrong:
                    c_order += 1
                    ex_order.append((O.show_full(phi), marking, target, s[:40], gua[:1] or pos[:1]))
    rec("backward: families (<= max_k) vs brute force", checked, c_other, ex_other)
    rec("backward: `already` and a non-empty 'minimal' set (B1)", checked, c_min, ex_min)
    rec("backward: `*_none` = 'no such set' while one exists (B2)", checked, c_trunc, ex_trunc)
    rec("backward: order() says no set / no guarantee while one exists (B2, B3)",
        checked, c_order, ex_order)
    rec("backward: memo changes nothing", checked, c_memo, ex_memo)

    # the cap refusal speaks as "no such set"
    phi = J.formalize(" & ".join(f"g{i}" for i in range(10)))
    m = {f"g{i}": O.Z for i in range(10)}
    r = B.backward(phi, m, "REFUTED")
    print(f"   over the cap: 'отказ' in result: {'отказ' in r}, possible_none "
          f"{r['possible_none']}; order(): {B.order(phi, m, 'REFUTED')!r}; "
          f"oracle: {{g0}} refutes alone")

    # what_to_check (the studio's door) vs the oracle
    bad, ex, n_w, bad_b1 = 0, [], 0, 0
    for i in range(n // 2):
        k = rng.randint(1, 4)
        names = [f"a{j}" for j in range(k)]
        phi = rand_formula(rng, names, rng.randint(1, 4))
        text = O.show_min(phi)
        marking = {a: rng.choice([O.Z, O.Z, O.T, O.F]) for a in sorted(O.atoms(phi))}
        unv = sorted(a for a, v in marking.items() if v == O.Z)
        if not unv:
            continue
        n_w += 1
        w = zfl.what_to_check(text, marking, unv)
        if "refused" in w:
            continue
        for tgt, key in (("EARNED", "EARNED"), ("REFUTED", "REFUTED"),
                         (frozenset({"EARNED", "REFUTED"}), "SETTLED")):
            pos, gua = O.families(phi, marking, tgt, True)
            already = () in pos
            got = w[key]
            want = {"already": already,
                    "guaranteed": [] if already else [list(S) for S in gua],
                    "possible": [] if already else [list(S) for S in pos],
                    "no_guaranteed_set": not gua,
                    "no_possible_set": not pos}
            got_cmp = {kk: got[kk] for kk in want}
            got_cmp["guaranteed"] = [list(S) for S in _code_family(got["guaranteed"])]
            got_cmp["possible"] = [list(S) for S in _code_family(got["possible"])]
            if got_cmp != want:
                if already:
                    bad_b1 += 1
                else:
                    bad += 1
                    ex.append((text, marking, key, got_cmp, want))
    rec("what_to_check vs the documented minimal families (outside B1)", n_w, bad, ex)
    rec("what_to_check: `already` beside a non-empty set (B1 at the studio door)",
        n_w, bad_b1, [])


# ================================================================= epoch
def _doc(rng):
    k = rng.randint(1, 4)
    names = [f"g{j}" for j in range(k)]
    n_ev = rng.randint(1, 3)
    evs = [f"e{j}" for j in range(n_ev)]
    phi = rand_formula(rng, names + (evs if rng.random() < 0.2 else []),
                       rng.randint(1, 4))
    rows, marking = [], {}
    for e in evs:
        st = rng.choice(["unverified", "verified"]) if e in O.atoms(phi) else "unverified"
        rows.append(dict(name=e, means="event", status=st,
                         ground="doc" if st == "verified" else ""))
        marking[e] = {"unverified": O.Z, "verified": O.T}[st]
    expiring = {}
    for a in names:
        st = rng.choice(["verified", "verified", "refuted", "unverified"])
        r = dict(name=a, means="m", status=st, ground="" if st == "unverified" else "doc")
        marking[a] = {"unverified": O.Z, "verified": O.T, "refuted": O.F}[st]
        if st != "unverified" and rng.random() < 0.7:
            r["expires_on"] = rng.choice(evs)
            expiring.setdefault(r["expires_on"], []).append(a)
        rows.append(r)
    if rng.random() < 0.4:
        # a DEFINED row over the plain rows: the floor must read THROUGH it
        body = rand_formula(rng, names, rng.randint(1, 3))
        rows.append(dict(name="d0", means="defined", status="defined",
                         ground=O.show_min(body)))
        marking["d0"] = ("defined", body)
        if rng.random() < 0.7:
            phi = (rng.choice(O.BIN), phi, "d0") if rng.random() < 0.6 else "d0"
    return phi, rows, marking, expiring


def s_epoch(seed, n):
    import zfl
    rng = random.Random(seed)
    bad, ex, docs, crossings = 0, [], 0, 0
    surv_neither, ex_neither = 0, []
    for i in range(n):
        phi, rows, marking, expiring = _doc(rng)
        if not expiring:
            continue
        text = O.show_min(phi)
        r = zfl.run({"claim": text, "rows": rows})
        if not r["ok"]:
            bad += 1
            ex.append(("refused", text, r["issues"]))
            continue
        docs += 1
        got = r["report"].get("epoch")
        want = []
        plain = {a: v for a, v in marking.items() if not isinstance(v, tuple)}

        def resolve(pm):
            out = dict(pm)
            for a, v in marking.items():
                if isinstance(v, tuple):
                    out[a] = O.kleene(v[1], pm)
            return {a: out[a] for a in sorted(O.atoms(phi))}
        m_b = resolve(plain)
        vb, gb = O.ev(phi, m_b), O.grade(phi, m_b)
        for ev_name in sorted(expiring):
            pa = dict(plain)
            for a in expiring[ev_name]:
                pa[a] = O.Z
            m_a = resolve(pa)
            va, ga = O.ev(phi, m_a), O.grade(phi, m_a)
            want.append({"event": ev_name, "expires": sorted(expiring[ev_name]),
                         "before": {"verdict": vb, "grade": gb},
                         "after": {"verdict": va, "grade": ga},
                         "survives": O.disposition_of(vb, gb) == O.disposition_of(va, ga)})
            crossings += 1
            reads = m_a != m_b
            if vb == va and reads and ga != "hereditary" and not O.constant(phi):
                surv_neither += 1
                ex_neither.append((text, ev_name, expiring[ev_name], f"{vb}/{gb} -> {va}/{ga}"))
        if got != want:
            bad += 1
            ex.append((text, rows, got, want))
    rec("epoch floor (zfl.run) vs one crossing per event", docs, bad, ex, crossings=crossings)
    rec("epoch: survivors that read the expiring ground and are neither "
        "independently grounded nor empty (E1, the comment)", crossings,
        surv_neither, ex_neither)

    # ztime.gstate / zexpire.expire vs the grades (the M dialect)
    import ztime
    import zexpire
    bad, ex = 0, []
    for i in range(n):
        k = rng.randint(1, 4)
        names = [f"a{j}" for j in range(k)]
        phi = rand_formula(rng, names, rng.randint(1, 5), consts=True)
        m = {a: rng.choice([O.T, O.F, O.Z]) for a in sorted(O.atoms(phi))}
        mM = {a: ("M" if v == O.Z else v) for a, v in m.items()}
        got = ztime.gstate(phi, mM)
        want = (O.ev(phi, m), {"hereditary": "H", "sound": "S",
                               "until-verification": "U"}[O.grade(phi, m)])
        if got != want:
            bad += 1
            ex.append((O.show_full(phi), m, got, want))
        ground = [a for a, v in m.items() if v != O.Z]
        if ground:
            a = rng.choice(ground)
            m2 = zexpire.expire(mM, a)
            want2 = dict(mM)
            want2[a] = "M"
            if m2 != want2 or zexpire.gstate(phi, m2) != (
                    O.ev(phi, {**m, a: O.Z}),
                    {"hereditary": "hereditary", "sound": "sound",
                     "until-verification": "until-verification"}[O.grade(phi, {**m, a: O.Z})]):
                bad += 1
                ex.append(("expire", O.show_full(phi), m, a))
    rec("ztime.gstate / zexpire.expire+gstate vs the grades", 2 * n, bad, ex)

    # EpochBoundary.epoch_boundary_iff on the depth-2 pool, all 9 markings
    pool = O.depth2_pool()
    bad, ex, n_e = 0, [], 0
    for phi in pool:
        c = O.constant(phi)
        for vals in product(O.VALS, repeat=2):
            n_e += 1
            if O.epoch_blind(phi, dict(zip("pq", vals))) != c:
                bad += 1
                ex.append((phi, vals))
    rec("EpochBoundary: epoch-blind iff constant (BFS reach, depth-2 pool)", n_e, bad, ex)
    frames = sum(1 for phi in pool if O.constant(phi))
    print(f"   zexpire §2: pool {len(pool)} formulas, constant over 9 markings {frames} "
          f"(docstring: 2,906 and 398)")
    RESULTS.append(dict(section="zexpire §2 numbers", pool=len(pool), frames=frames))
    ztime_numbers(pool)


def ztime_numbers(pool):
    """Recompute ztime.py's docstring numbers from the oracle's grades,
    over the oracle's own pool, walking the definitions in its docstring."""
    G = {"hereditary": "H", "sound": "S", "until-verification": "U"}

    def st(phi, m):
        return (O.ev(phi, m), G[O.grade(phi, m)])
    trans, ticks, her_broken, zc = {}, 0, 0, 0
    for phi in pool:
        names = sorted(O.atoms(phi))
        for combo in product(O.VALS, repeat=len(names)):
            m = dict(zip(names, combo))
            marks = [a for a in names if m[a] == O.Z]
            if not marks:
                continue
            s1 = st(phi, m)
            if not isinstance(phi, str) and s1[0] == O.Z:
                zc += 1
            for a in marks:
                for v in (O.T, O.F):
                    s2 = st(phi, {**m, a: v})
                    trans[(s1, s2)] = trans.get((s1, s2), 0) + 1
                    ticks += 1
                    if s1[1] == "H" and s2 != s1:
                        her_broken += 1
    u2h = sum(c for (a, b), c in trans.items() if a[1] == "U" and b[1] == "H")
    s2u = sum(c for (a, b), c in trans.items() if a[1] == "S" and b[1] == "U")
    into_s = sum(c for (a, b), c in trans.items() if b[1] == "S")
    got = dict(formulas=len(pool), ticks=ticks, her_broken=her_broken,
               z_compound=zc, u_to_h=u2h, s_to_u=s2u, into_S=into_s)
    doc = dict(formulas=2906, ticks=29812, her_broken=0, z_compound=0,
               u_to_h=14818, s_to_u=108, into_S=0)
    print(f"   ztime §1 recomputed: {got}")
    print(f"   ztime §1 docstring : {doc}")
    RESULTS.append(dict(section="ztime §1 numbers", recomputed=got, docstring=doc))

    # §5: 3 atoms, depth <= 2, all marked, genuine entries into S
    pool3 = O.depth2_pool(("p", "q", "r"))
    m0 = {"p": O.Z, "q": O.Z, "r": O.Z}
    h_ticks = genuine = 0
    for phi in pool3:
        g0 = G[O.grade(phi, m0)]
        for a in "pqr":
            for v in (O.T, O.F):
                h_ticks += 1
                if G[O.grade(phi, {**m0, a: v})] == "S" and g0 != "S":
                    genuine += 1
    print(f"   ztime §5 recomputed: formulas {len(pool3)}, ticks {h_ticks}, genuine {genuine} "
          f"(docstring: 13,059 × 78,354, 0)")
    RESULTS.append(dict(section="ztime §5 numbers", formulas=len(pool3),
                        ticks=h_ticks, genuine=genuine))
    # §6: the selector witness
    X = ("or", ("not", ("not", "p")), ("or", "q", ("not", "q")))
    w = ("or", ("and", "a", X), ("and", ("not", "a"), "p"))
    path = [{"a": O.Z, "p": O.Z, "q": O.Z}, {"a": O.T, "p": O.Z, "q": O.Z},
            {"a": O.T, "p": O.T, "q": O.Z}]
    print(f"   ztime §6 witness grades: {[G[O.grade(w, m)] for m in path]} "
          f"(docstring: U, S, H); depth of the witness: {depth(w)} connectives "
          f"(docstring says 'depth 3' in the header and 'depth 4' in §2's print)")


def depth(phi):
    return 0 if isinstance(phi, str) else 1 + max(depth(s) for s in phi[1:])


# ============================================================== tableaux
SIGN_ALL = [frozenset(s) for k in range(0, 4)
            for s in __import__("itertools").combinations(O.VALS, k)]


def s_tableau(seed, n):
    import tableau as TB
    rng = random.Random(seed)
    # exhaustive: every formula up to 5 nodes over {p, q, T, F, Z}, every sign
    forms = all_formulas(["p", "q", "T", "F", "Z"], 5)
    bad, ex, cnt = 0, [], 0
    for f in forms:
        for s in SIGN_ALL:
            cnt += 1
            if TB.tableau_closes([(s, f)]) != (not O.sat_signed([(s, f)])):
                bad += 1
                ex.append((s, f))
    rec(f"tableau: every formula <= 5 nodes x every sign ({len(forms)} formulas)",
        cnt, bad, ex)
    # random signed sets
    bad, ex = 0, []
    for i in range(n):
        k = rng.randint(1, 4)
        names = [f"a{j}" for j in range(rng.randint(1, 4))]
        nodes = [(rng.choice(SIGN_ALL), rand_formula(rng, names, rng.randint(0, 4), True))
                 for _ in range(k)]
        if TB.tableau_closes(nodes) != (not O.sat_signed(nodes)):
            bad += 1
            ex.append(nodes)
    rec("tableau: random signed sets vs satisfiability", n, bad, ex)
    # prove vs entailment
    bad, ex = 0, []
    for i in range(n):
        names = [f"a{j}" for j in range(rng.randint(1, 4))]
        prems = [rand_formula(rng, names, rng.randint(0, 3), True)
                 for _ in range(rng.randint(0, 3))]
        concl = rand_formula(rng, names, rng.randint(0, 3), True)
        if TB.prove(prems, concl) != O.entails(prems, concl):
            bad += 1
            ex.append((prems, concl))
    rec("tableau.prove vs entailment", n, bad, ex)
    # zsequent: identity, weakening, cut (both covering pairs)
    ST, SF, SP, SN = (frozenset({O.T}), frozenset({O.F}),
                      frozenset({O.T, O.Z}), frozenset({O.F, O.Z}))
    bad, ex, fired = 0, [], 0
    for i in range(n):
        names = [f"a{j}" for j in range(rng.randint(1, 3))]
        S = [(rng.choice([ST, SF, SP, SN]), rand_formula(rng, names, rng.randint(0, 3)))
             for _ in range(rng.randint(0, 3))]
        phi = rand_formula(rng, names, rng.randint(0, 3))
        if not TB.tableau_closes([(ST, phi), (SN, phi)]):
            bad += 1
            ex.append(("identity", phi))
        cS = TB.tableau_closes(S)
        if cS and not TB.tableau_closes(S + [(rng.choice([ST, SF, SP, SN]), phi)]):
            bad += 1
            ex.append(("weakening", S, phi))
        for a, b in ((ST, SN), (SF, SP)):
            if TB.tableau_closes(S + [(a, phi)]) and TB.tableau_closes(S + [(b, phi)]):
                fired += 1
                if not cS:
                    bad += 1
                    ex.append(("cut", S, phi))
    rec("zsequent: identity, weakening, cut", n, bad, ex, cut_fired=fired)


# ==================================================================== fo
def rand_fo(rng, depth, bound, free_ok=("x",)):
    vars_ = list(bound) + list(free_ok)
    if depth == 0 or rng.random() < 0.3:
        if rng.random() < 0.25:
            return ("R", rng.choice(vars_), rng.choice(vars_))
        return (rng.choice(["P", "Q"]), rng.choice(vars_))
    r = rng.random()
    if r < 0.3:
        v = rng.choice(["y", "z", "x"])
        return (rng.choice(["all", "ex"]), v, rand_fo(rng, depth - 1, tuple(sorted(set(bound) | {v})), free_ok))
    if r < 0.45:
        return ("not", rand_fo(rng, depth - 1, bound, free_ok))
    return (rng.choice(O.BIN), rand_fo(rng, depth - 1, bound, free_ok),
            rand_fo(rng, depth - 1, bound, free_ok))


def _to_quant_interp(I, dom):
    """The oracle's cell dict -> quantifiers.ev_fo's tuple layout."""
    out = {}
    for p in ("P", "Q"):
        out[p] = tuple(I.get((p, d), O.Z) for d in dom)
    out["R"] = tuple(tuple(I.get(("R", a, b), O.Z) for b in dom) for a in dom)
    return out


def s_fo(seed, n):
    import quantifiers as QF
    import tableau_fo as TF
    import zfo
    rng = random.Random(seed)
    # ev_fo vs the folds
    bad, ex = 0, []
    for i in range(n):
        phi = rand_fo(rng, rng.randint(1, 4), ())
        dom = list(range(rng.randint(1, 3)))
        cells = [("P", d) for d in dom] + [("Q", d) for d in dom] + \
                [("R", a, b) for a in dom for b in dom]
        I = {c: rng.choice(O.VALS) for c in cells}
        env = {"x": rng.choice(dom)}
        if QF.ev_fo(phi, dom, _to_quant_interp(I, dom), env) != O.fo_ev(phi, dom, I, env):
            bad += 1
            ex.append((phi, dom, I, env))
    rec("quantifiers.ev_fo vs the strict folds", n, bad, ex)

    # tableau_fo.prove_fo vs semantics on a fixed domain (x read as 0)
    bad, ex, cnt = 0, [], 0
    for i in range(n // 4):
        prems = [rand_fo(rng, rng.randint(0, 2), ()) for _ in range(rng.randint(0, 2))]
        concl = rand_fo(rng, rng.randint(0, 3), ())
        forms = prems + [concl]
        nR = sum(str(f).count("'R'") for f in forms)
        for size_ in (1, 2, 3):
            dom = list(range(size_))
            ncells = 0
            ar = {}
            for f in forms:
                O.fo_preds(f, ar)
            ncells = sum(size_ ** k for k in ar.values())
            if ncells > 9:
                continue
            cnt += 1
            got = TF.prove_fo(prems, concl, dom)
            want = O.fo_countermodel(prems, concl, dom, consts_to={"x": 0}) is None
            if got != want:
                bad += 1
                ex.append((prems, concl, size_, got, want))
    rec("tableau_fo.prove_fo vs finite semantics (domains 1-3, <= 9 cells)", cnt, bad, ex)

    # zfo.prove over arbitrary domains: valid => no finite countermodel;
    # countermodel => it checks out under the oracle's evaluation
    bad, ex, stats = 0, [], {"valid": 0, "countermodel": 0, "budget": 0}
    for i in range(n // 4):
        prems = [rand_fo(rng, rng.randint(0, 2), (), ("#a",)) for _ in range(rng.randint(0, 2))]
        concl = rand_fo(rng, rng.randint(0, 3), (), ("#a",))
        verdict, info = zfo.prove(prems, concl, budget_units=400)
        stats[verdict] += 1
        if verdict == "valid":
            for size_ in (1, 2, 3):
                ar = {}
                for f in prems + [concl]:
                    O.fo_preds(f, ar)
                if sum(size_ ** k for k in ar.values()) > 9:
                    continue
                cm = O.fo_countermodel(prems, concl, list(range(size_)))
                if cm is not None:
                    bad += 1
                    ex.append(("valid but", prems, concl, cm))
                    break
        elif verdict == "countermodel":
            values, dom = info
            ok = all(O.fo_ev(p, dom, values, {}) == O.T for p in prems) and \
                O.fo_ev(concl, dom, values, {}) != O.T
            if not ok:
                bad += 1
                ex.append(("countermodel does not check", prems, concl, values, dom))
    rec("zfo.prove: valid has no finite countermodel; countermodels check",
        n // 4, bad, ex, **stats)


SECTIONS = {"parse": s_parse, "backward": s_backward, "epoch": s_epoch,
            "tableau": s_tableau, "fo": s_fo}
DEFAULT_N = {"parse": 20000, "backward": 1500, "epoch": 1500, "tableau": 20000, "fo": 4000}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20260928)
    ap.add_argument("--only", default=",".join(SECTIONS))
    ap.add_argument("--n", type=int, default=None)
    ap.add_argument("--json", action="store_true")
    a = ap.parse_args()
    for s in a.only.split(","):
        t0 = time.time()
        print(f"== {s} (seed {a.seed})")
        SECTIONS[s](a.seed, a.n or DEFAULT_N[s])
        print(f"   {time.time() - t0:.1f} s")
    if a.json:
        print(json.dumps(RESULTS, ensure_ascii=False, default=str))


if __name__ == "__main__":
    main()
