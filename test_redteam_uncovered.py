# -*- coding: utf-8 -*-
"""
The stand of the red team of the UNCOVERED core (2026-09-28).

    python3 test_redteam_uncovered.py          # seeded, well under 90 s

It passes when nothing was found. On the code it was written against
(master @ 1af886b) it FAILS, and each failing check pins one finding with
its minimal reproduction:

  B1  CODE       zbackward lists non-empty "minimal" sets beside `already`
                 (the empty set qualifies) — and so does zfl.what_to_check.
  B2  CODE       a TRUNCATED search reports "no such set" (possible_none /
                 guaranteed_none), and order() turns it into "НЕТ НАБОРА:
                 недостижима никакой проверкой" / "ГАРАНТИИ НЕТ".
  B3  CODE       a search REFUSED at the cap reports possible_none = True,
                 and order() says "НЕТ НАБОРА" where one ground settles it.
  P1  DOCUMENTS  the parser's precedence and associativity are stated
                 nowhere, and four readings differ from the usual convention.
  E1  DOCUMENTS  zfl.run's epoch comment: "a survivor here is either
                 independently grounded or empty" — `~p` survives the expiry
                 of its only ground.

Beside the pins it runs a small seeded sweep of every target against the
independent oracle (`inventory/probes/redteam_uncovered_oracle.py`, which
imports none of the code under test); those sweeps found nothing and must
stay clean. NOT registered in run_all.py (the task says so).
"""
import os
import random
import re
import sys
import time
from itertools import product

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "inventory", "probes"))

import redteam_uncovered_oracle as O          # noqa: E402
import redteam_uncovered_search as S          # noqa: E402

import zbackward as B                         # noqa: E402
import zfl                                    # noqa: E402
import ztljudge as J                          # noqa: E402

SEED = 20260928
FAILED = []


def check(name, ok, detail=""):
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}" + (f"\n         {detail}" if not ok else ""))
    if not ok:
        FAILED.append(name)


def rows(*rs):
    return [dict(name=n, means="m", status=s, ground=g,
                 **({"expires_on": e} if e else {})) for n, s, g, e in rs]


# ------------------------------------------------------------------ pins
def pin_b1():
    # the kernel: p | q with p verified is EARNED already; the documented
    # minimal family is {∅}, and {q} is not minimal (∅ ⊂ {q} qualifies)
    r = B.backward(("or", "p", "q"), {"p": "T", "q": "Z"}, "EARNED")
    pos, gua = O.families(("or", "p", "q"), {"p": "T", "q": "Z"}, "EARNED")
    check("B1 zbackward: `already` and no non-empty set listed",
          not (r["already"] and (r["possible"] or r["guaranteed"])),
          f"already={r['already']}, possible={r['possible']}, guaranteed={r['guaranteed']}; "
          f"oracle minimal families {pos} / {gua}")
    # a ground foreign to the formula is offered as a 'minimal' set
    r = B.backward("p", {"p": "T", "r": "Z"}, "EARNED")
    check("B1 zbackward: no set made of an atom the formula does not contain",
          not any("r" in s for s in r["possible"] + r["guaranteed"]),
          f"backward('p', {{p:T, r:Z}}, EARNED) -> possible {r['possible']}, "
          f"guaranteed {r['guaranteed']}")
    # the other face: ∅ guarantees, yet 'no guaranteed set'
    r = B.backward(("not", "a"), {"a": "Z"}, "F", by_disposition=False)
    check("B1 zbackward: guaranteed_none is not claimed when the empty set guarantees",
          not (r["already"] and r["guaranteed_none"]),
          f"backward(~a, {{a:Z}}, 'F', by value) -> already {r['already']}, "
          f"guaranteed_none {r['guaranteed_none']}")
    # at the studio's door: the judge says q does not matter; what_to_check
    # lists q as the minimal set to check
    doc = {"claim": "p | q", "rows": rows(("p", "verified", "d", None),
                                          ("q", "unverified", "", None))}
    rep = zfl.run(doc)["report"]
    w = rep["what_to_check"]["EARNED"]
    check("B1 zfl.what_to_check: EARNED already -> no set to check",
          not (w["already"] and w["guaranteed"]),
          f"judge: {rep['judge']['disposition']} ({rep['judge']['why']}); "
          f"what_to_check EARNED = {w}")


def pin_b2():
    phi = J.formalize("a & b & c & d & e")
    m = {k: "Z" for k in "abcde"}
    s = B.order(phi, m, "EARNED")
    pos, gua = O.families(phi, m, "EARNED")
    check("B2 order(): a truncated search does not say 'no set'",
          not s.startswith("НЕТ НАБОРА"),
          f"order(a&b&c&d&e, all Z, EARNED) = {s!r}; oracle: possible {pos}")
    r = B.backward(phi, m, "EARNED")
    check("B2 backward: possible_none is not claimed beside the truncation note",
          not (r["possible_none"] and "не_искал_дальше" in r),
          f"possible_none={r['possible_none']}, note={r.get('не_искал_дальше')!r}")
    s = B.order(phi, m, B.TERMINAL)
    pos, gua = O.families(phi, m, B.TERMINAL)
    check("B2 order(): a truncated search does not say 'no guarantee'",
          not s.startswith("ГАРАНТИИ НЕТ"),
          f"order(a&b&c&d&e, all Z, SETTLED) = {s[:60]!r}…; oracle guaranteed {gua}")


def pin_b3():
    phi = J.formalize(" & ".join(f"g{i}" for i in range(10)))
    m = {f"g{i}": "Z" for i in range(10)}
    r = B.backward(phi, m, "REFUTED")
    check("B3 backward: a refusal at the cap is not 'no such set'",
          not ("отказ" in r and r["possible_none"]),
          f"'отказ' present and possible_none={r['possible_none']}")
    s = B.order(phi, m, "REFUTED")
    one = B.backward(phi, m, "REFUTED", cap_grounds=10, max_k=1)["possible"]
    check("B3 order(): over the cap it does not say 'unreachable by any check'",
          not s.startswith("НЕТ НАБОРА"),
          f"order(g0&…&g9, all Z, REFUTED) = {s!r}; one ground refutes: {one[:3]}…")


def pin_p1():
    # P1 is a finding for the DOCUMENTS: the reading is consistent (the
    # sweeps below), but nothing states it, and the arrow reads LEFT.
    got = J.formalize("a -> b -> c")
    assert got == ("imp", ("imp", "a", "b"), "c"), got      # the measured reading
    texts = []
    for f in ("SPEC.md", "ONBOARDING.md", "ztljudge.py", "JUDGE-API.md", "zfldoc.py"):
        p = os.path.join(HERE, f)
        if os.path.exists(p):
            texts.append(open(p, encoding="utf-8").read())
    stated = any(re.search(r"(?i)(left[- ]assoc|левоассоц|precedence|приоритет"
                           r"|binds (tighter|more tightly))", t) for t in texts)
    check("P1 the parser's precedence / associativity is stated in a document",
          stated,
          "formalize('a -> b -> c') = (a → b) → c; & > | > ^ > -> > =, all left; "
          "no statement in SPEC.md, ONBOARDING.md, ztljudge.py, JUDGE-API.md, "
          "zfldoc.py (the studio's operator reference)")


def pin_e1():
    doc = {"claim": "~p", "rows": rows(("ev", "unverified", "", None),
                                       ("p", "verified", "doc", "ev"))}
    e = zfl.run(doc)["report"]["epoch"][0]
    # the comment: "a verdict that survives every crossing reads none of its
    # grounds (EpochBoundary), so a survivor here is either independently
    # grounded or empty"
    neither = (e["survives"] and e["after"]["grade"] != "hereditary"
               and not O.constant(("not", "p")))
    check("E1 an epoch survivor is independently grounded or empty (zfl.run comment)",
          not neither,
          f"claim ~p, its only ground p expires: {e['before']} -> {e['after']}, "
          f"survives={e['survives']}; ~p reads p and is not constant")


# ---------------------------------------------------------------- sweeps
def sweep_parse():
    rng = random.Random(SEED)
    bad = 0
    for i in range(1500):
        phi = S.rand_formula(rng, ["p", "q", "r", "T", "Z"], rng.randint(1, 6))
        for text in (O.show_min(phi), O.show_min(phi, "unicode")):
            bad += J.formalize(text) != phi
        bad += J.formalize(J._show(phi)) != phi
    alphabet = ["p", "~", "&", "|", "->", "^", "=", "(", ")"]
    n = 0
    for L in range(0, 6):
        for toks in product(alphabet, repeat=L):
            text = " ".join(toks)
            n += 1
            try:
                a = J.formalize(text)
            except ValueError:
                a = None
            try:
                b = O.parse(text)
            except O.Refused:
                b = None
            bad += a != b
    check(f"sweep parse: 4500 minimal/printed texts + {n} token strings", bad == 0,
          f"{bad} disagreements")


def sweep_backward():
    rng = random.Random(SEED)
    bad = n = 0
    memo_bad = 0
    for i in range(120):
        names = [f"a{j}" for j in range(rng.randint(1, 4))]
        phi = S.rand_formula(rng, names, rng.randint(1, 4))
        m = {a: rng.choice(["Z", "Z", "T", "F"]) for a in sorted(O.atoms(phi))}
        memo = {}
        for tgt in ("EARNED", "REFUTED", B.TERMINAL):
            n += 1
            r = B.backward(phi, m, tgt)
            r2 = B.backward(phi, m, tgt, memo=memo)
            memo_bad += r != r2
            pos, gua = O.families(phi, m, tgt)
            if r["already"] != (() in pos):
                bad += 1
            elif () not in pos:
                bad += (S._code_family(r["possible"]) != [s for s in pos if len(s) <= 4]
                        or S._code_family(r["guaranteed"]) != [s for s in gua if len(s) <= 4])
    check(f"sweep backward: {n} families outside B1-B3 match brute force", bad == 0,
          f"{bad} disagreements")
    check(f"sweep backward: the memo changes nothing ({n} calls)", memo_bad == 0,
          f"{memo_bad} differ")


def sweep_epoch():
    rng = random.Random(SEED)
    bad = docs = 0
    for i in range(150):
        phi, rws, marking, expiring = S._doc(rng)
        if not expiring:
            continue
        r = zfl.run({"claim": O.show_min(phi), "rows": rws})
        docs += 1
        plain = {a: v for a, v in marking.items() if not isinstance(v, tuple)}

        def resolve(pm):
            out = dict(pm)
            for a, v in marking.items():
                if isinstance(v, tuple):
                    out[a] = O.kleene(v[1], pm)
            return {a: out[a] for a in sorted(O.atoms(phi))}
        mb = resolve(plain)
        for e in r["report"]["epoch"]:
            pa = dict(plain)
            for a in expiring[e["event"]]:
                pa[a] = "Z"
            ma = resolve(pa)
            want = ({"verdict": O.ev(phi, mb), "grade": O.grade(phi, mb)},
                    {"verdict": O.ev(phi, ma), "grade": O.grade(phi, ma)})
            bad += (e["before"], e["after"]) != want or \
                e["survives"] != (O.disposition_of(want[0]["verdict"], want[0]["grade"]) == O.disposition_of(want[1]["verdict"], want[1]["grade"]))
    check(f"sweep epoch: {docs} documents, every crossing vs the oracle", bad == 0,
          f"{bad} disagreements")
    pool = O.depth2_pool()
    frames = sum(O.constant(p) for p in pool)
    check("sweep epoch: zexpire's census (2,906 formulas, 398 frames)",
          (len(pool), frames) == (2906, 398), f"{len(pool)}, {frames}")


def sweep_tableau_fo():
    import tableau as TB
    import tableau_fo as TF
    import quantifiers as QF
    import zfo
    rng = random.Random(SEED)
    bad = 0
    forms = S.all_formulas(["p", "q", "T", "Z"], 4)
    for f in forms:
        for s in S.SIGN_ALL:
            bad += TB.tableau_closes([(s, f)]) != (not O.sat_signed([(s, f)]))
    for i in range(300):
        names = [f"a{j}" for j in range(rng.randint(1, 3))]
        prems = [S.rand_formula(rng, names, rng.randint(0, 3), True) for _ in range(rng.randint(0, 2))]
        concl = S.rand_formula(rng, names, rng.randint(0, 3), True)
        bad += TB.prove(prems, concl) != O.entails(prems, concl)
    check(f"sweep tableau: {len(forms)} formulas x 8 signs + 300 entailments", bad == 0,
          f"{bad} disagreements")
    bad = 0
    for i in range(300):
        phi = S.rand_fo(rng, rng.randint(1, 3), ())
        dom = list(range(rng.randint(1, 2)))
        cells = [("P", d) for d in dom] + [("Q", d) for d in dom] + \
                [("R", a, b) for a in dom for b in dom]
        I = {c: rng.choice(O.VALS) for c in cells}
        bad += QF.ev_fo(phi, dom, S._to_quant_interp(I, dom), {"x": 0}) != \
            O.fo_ev(phi, dom, I, {"x": 0})
    for i in range(80):
        prems = [S.rand_fo(rng, rng.randint(0, 2), ()) for _ in range(rng.randint(0, 1))]
        concl = S.rand_fo(rng, rng.randint(0, 2), ())
        ar = {}
        for f in prems + [concl]:
            O.fo_preds(f, ar)
        if sum(2 ** k for k in ar.values()) <= 8:
            bad += TF.prove_fo(prems, concl, [0, 1]) != \
                (O.fo_countermodel(prems, concl, [0, 1], {"x": 0}) is None)
    for i in range(60):
        prems = [S.rand_fo(rng, rng.randint(0, 2), (), ("#a",)) for _ in range(rng.randint(0, 1))]
        concl = S.rand_fo(rng, rng.randint(0, 2), (), ("#a",))
        v, info = zfo.prove(prems, concl, budget_units=300)
        if v == "countermodel":
            vals, dom = info
            bad += not (all(O.fo_ev(p, dom, vals, {}) == "T" for p in prems)
                        and O.fo_ev(concl, dom, vals, {}) != "T")
        elif v == "valid":
            bad += O.fo_countermodel(prems, concl, [0]) is not None
    check("sweep first order: ev_fo, prove_fo, zfo.prove vs the oracle", bad == 0,
          f"{bad} disagreements")


if __name__ == "__main__":
    t0 = time.time()
    print("RED TEAM — the uncovered core (2026-09-28)")
    for f in (pin_b1, pin_b2, pin_b3, pin_p1, pin_e1,
              sweep_parse, sweep_backward, sweep_epoch, sweep_tableau_fo):
        f()
    print(f"\n{len(FAILED)} failing checks, {time.time() - t0:.1f} s")
    if FAILED:
        print("RED: " + "; ".join(FAILED))
        sys.exit(1)
    print("GREEN: nothing found")
