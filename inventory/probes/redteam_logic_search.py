# -*- coding: utf-8 -*-
"""
redteam_logic_search — the logic core against its own definitions (2026-09-27).

Every check compares the CODE (ztl, zmodal, zverify, ztljudge, fixedpoint,
zpassport) with the independent oracle `redteam_logic_oracle.py`, written from
the documents. A disagreement is printed with the formula and marking; the
counts are the space searched. Seeded: section S uses random.Random(f"{S}:{seed}").

Run:
  python3 inventory/probes/redteam_logic_search.py --seed 20260927 --scale 1
  python3 inventory/probes/redteam_logic_search.py --only grade --scale 0.1
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

import redteam_logic_oracle as O                     # noqa: E402
import ztl                                           # noqa: E402
import zmodal                                        # noqa: E402
import zverify                                       # noqa: E402
import ztljudge                                      # noqa: E402
import fixedpoint                                    # noqa: E402
import zpassport                                     # noqa: E402

ATOMS10 = [f"p{i}" for i in range(10)]
OUT = {}


def rec(section, n, bad, examples):
    OUT[section] = {"checked": n, "disagreements": bad, "examples": examples[:5]}
    print(f"  {section:34s} checked {n:>10,}   disagreements {bad}", flush=True)
    for e in examples[:3]:
        print("     ", e)


def to_mark(m):
    """oracle marking (T/F/Z) -> zverify dialect (T/F/'M')."""
    return {a: ("M" if v == "Z" else v) for a, v in m.items()}


# ------------------------------------------------------------------ sections
def s_eval(seed, n):
    """ztl.ev, the recursive and iterative paths, zmodal.ztl_eval and the
    eager register of fixedpoint against the oracle's value."""
    rnd = random.Random(f"eval:{seed}")
    bad, ex = 0, []
    for _ in range(n):
        k = rnd.randint(1, 10)
        ats = ATOMS10[:k]
        phi = O.random_formula(rnd, rnd.randint(0, 6), ats)
        env = {a: rnd.choice(O.VALS) for a in ats}
        want = O.ev(phi, env)
        got = (ztl.ev(phi, env), ztl._ev_rec(phi, env), ztl._ev_iter(phi, env),
               zmodal.ztl_eval(phi, {a: ("M" if v == "Z" else v) for a, v in env.items()}),
               fixedpoint.ev_reg(phi, env, fixedpoint.EAGER))
        if any(g != want for g in got) or ztl.atoms(phi) != O.atoms(phi):
            bad += 1
            ex.append((ztl.show(phi), env, want, got))
    # deep chains: the iterative fallback
    for depth in (500, 1500, 5000):
        for op in O.OPS:
            phi = "p0"
            for i in range(depth):
                phi = (op, phi, ATOMS10[i % 10]) if i % 7 else ("not", phi)
            env = {a: rnd.choice(O.VALS) for a in ATOMS10}
            n += 1
            if ztl.ev(phi, env) != O.ev(phi, env):
                bad += 1
                ex.append(("deep", depth, op))
    rec("eval: ev / _ev_rec / _ev_iter / ztl_eval / ev_reg", n, bad, ex)


def s_exhaustive(seed, size):
    """Every formula up to `size` nodes over {p, q, T, F, Z}, every marking of
    p, q: value, classical agreement on T/F markings, grade."""
    leaves = ["p", "q", "T", "F", "Z"]
    n = bad = 0
    ex = []
    nf = 0
    for s in range(1, size + 1):
        for phi in O.all_formulas(s, leaves):
            nf += 1
            ats = sorted(O.atoms(phi))
            for combo in product(O.VALS, repeat=len(ats)):
                env = dict(zip(ats, combo))
                n += 1
                if ztl.ev(phi, env) != O.ev(phi, env):
                    bad += 1
                    ex.append(("ev", ztl.show(phi), env))
                    continue
                if zverify.grade(phi, to_mark(env)) != O.grade(phi, env):
                    bad += 1
                    ex.append(("grade", ztl.show(phi), env,
                               zverify.grade(phi, to_mark(env)), O.grade(phi, env)))
    rec(f"exhaustive <= {size} nodes ({nf:,} formulas)", n, bad, ex)


def s_classical(seed, n):
    """ClassicalAgreement.evalF_agrees: on T/F markings ZTL is classical.
    ztl_taut_is_classical: a formula T under every marking is classically
    valid. not_conversely: p -> p."""
    rnd = random.Random(f"classical:{seed}")
    bad, ex, taut = 0, [], 0
    for _ in range(n):
        ats = ATOMS10[:rnd.randint(1, 4)]
        phi = O.random_formula(rnd, rnd.randint(0, 5), ats, p_const=0.0)
        env = {a: rnd.choice((O.T, O.F)) for a in ats}
        if (ztl.ev(phi, env) == O.T) != O.classical(phi, env):
            bad += 1
            ex.append(("agree", ztl.show(phi), env))
        # ZTL-valid (every T/F/Z marking) => classically valid
        ztl_valid = all(ztl.ev(phi, dict(zip(ats, c))) == O.T
                        for c in product(O.VALS, repeat=len(ats)))
        if ztl_valid:
            taut += 1
            if not all(O.classical(phi, dict(zip(ats, c)))
                       for c in product((O.T, O.F), repeat=len(ats))):
                bad += 1
                ex.append(("taut", ztl.show(phi)))
    p2p = ("imp", "p", "p")
    if not (all(O.classical(p2p, {"p": v}) for v in "TF") and ztl.ev(p2p, {"p": "Z"}) == "F"):
        bad += 1
        ex.append("not_conversely")
    rec(f"classical agreement / taut ({taut:,} ZTL-valid)", n + 1, bad, ex)


def s_grade(seed, n):
    """zverify.grade / hereditary_bit / stable_bit against the definitions,
    and the budget property (a budget only weakens, never changes)."""
    rnd = random.Random(f"grade:{seed}")
    WEAKER = {"hereditary": {"hereditary", "sound-or-better", "undetermined"},
              "sound": {"sound", "sound-or-better", "undetermined"},
              "until-verification": {"until-verification", "undetermined"}}
    bad, ex = 0, []
    for _ in range(n):
        ats = ATOMS10[:rnd.randint(1, 7)]
        phi = O.random_formula(rnd, rnd.randint(0, 6), ats)
        env = {a: rnd.choice((O.T, O.F, O.Z, O.Z)) for a in ats}
        mk = to_mark(env)
        want = O.grade(phi, env)
        g = zverify.grade(phi, mk)
        h = zverify.hereditary_bit(phi, mk)
        st = zverify.stable_bit(phi, mk)
        ok = (g == want and h == O.hereditary(phi, env) and st == O.sound(phi, env))
        b = rnd.choice([1, 3, 9, 27, 81, 243])
        gb = zverify.grade(phi, mk, budget=b)
        if gb not in WEAKER[want]:
            ok = False
        # the marking of a whole document: foreign marks must not matter
        extra = dict(mk)
        extra.update({f"x{i}": "M" for i in range(3)})
        if zverify.grade(phi, extra) != want:
            ok = False
        if not ok:
            bad += 1
            ex.append((ztl.show(phi), env, want, g, h, st, b, gb))
    rec("grade / hereditary / sound / budget", n, bad, ex)


def s_judge(seed, n):
    """ztljudge.judge: verdict, grade, unverified, absent, disposition, the
    lazy register and the receipt (no unverified atom off the label can move
    the verdict: `receipt_complete_greedy`)."""
    rnd = random.Random(f"judge:{seed}")
    bad, ex = 0, []
    l1, l1_ex = 0, []
    for _ in range(n):
        ats = ATOMS10[:rnd.randint(1, 7)]
        phi = O.random_formula(rnd, rnd.randint(1, 6), ats)
        text = O.text_full(phi)
        marks = {}
        for a in ats:
            r = rnd.random()
            if r < 0.4:
                continue                              # left out: the mark
            marks[a] = rnd.choice(["T", "F", "Z", "E"])
        r = ztljudge.judge(text, marks)
        present = O.atoms(phi)
        full = {a: marks.get(a, "Z") for a in present}
        kern = {a: ("Z" if v == "E" else v) for a, v in full.items()}
        v = O.ev(phi, kern)
        g = O.grade(phi, kern)
        unv = sorted(a for a in present if full[a] == "Z")
        gone = sorted(a for a in present if full[a] == "E")
        disp = O.disposition(v, g, unv, gone)
        lv = O.ev_lazy(phi, kern)
        problems = []
        if ztljudge.formalize(text) != phi:
            problems.append("parse")
        if r["verdict"] != v:
            problems.append(("verdict", r["verdict"], v))
        if r["grade"] != g:
            problems.append(("grade", r["grade"], g))
        if r["unverified"] != unv or r["absent"] != gone:
            problems.append(("unverified/absent", r["unverified"], r["absent"]))
        if r["disposition"] != disp:
            problems.append(("disposition", r["disposition"], disp))
        if r["lazy"] != lv:
            problems.append(("lazy", r["lazy"], lv))
        # the receipt: every unverified atom NOT pending cannot move ev
        if lv == "Z":
            idle = [a for a in unv + gone if a not in r["pending"]]
            for a in idle:
                for val in ("T", "F"):
                    k2 = dict(kern)
                    k2[a] = val
                    if O.ev(phi, k2) != v:
                        problems.append(("receipt", a, val))
        else:
            if r["pending"]:
                problems.append(("pending-when-decided", r["pending"]))
        if problems:
            kinds = {pr if isinstance(pr, str) else pr[0] for pr in problems}
            has_const = bool(O.atoms(phi) != set(_leaves(phi)))
            if has_const and kinds <= {"lazy", "pending-when-decided", "receipt"}:
                l1 += 1                     # finding L1: constants read as marks
                l1_ex.append((text, marks, problems))
            else:
                bad += 1
                ex.append((text, marks, problems))
    rec("judge: verdict/grade/disposition/lazy", n, bad, ex)
    OUT["judge_attributed_L1"] = l1
    print(f"  {'   of which L1 (constants in lazy)':34s} {l1:>10,}  (not counted above)")
    for e in l1_ex[:2]:
        print("     ", e)


def _leaves(phi):
    if isinstance(phi, str):
        return [phi]
    out = []
    for c in phi[1:]:
        out += _leaves(c)
    return out


def s_parse(seed, n):
    """ztljudge.formalize on fully parenthesised text gives back the AST."""
    rnd = random.Random(f"parse:{seed}")
    bad, ex = 0, []
    for _ in range(n):
        phi = O.random_formula(rnd, rnd.randint(0, 6), ATOMS10[:5])
        if ztljudge.formalize(O.text_full(phi)) != phi:
            bad += 1
            ex.append(O.text_full(phi))
    rec("parse: formalize(full parens)", n, bad, ex)


def s_passport(seed, n):
    """zpassport.passports against the oracle on random systems of 1-5
    sentences over Tr(names), constants and up to 2 free inputs."""
    rnd = random.Random(f"passport:{seed}")
    bad, ex = 0, []
    for _ in range(n):
        k = rnd.randint(1, 5)
        names = [f"s{i}" for i in range(k)]
        pool = names + (["T", "F", "Z"] if rnd.random() < 0.5 else [])
        system = {s: O.random_formula(rnd, rnd.randint(0, 3), pool, p_const=0.0)
                  for s in names}
        lfp, kind = O.passports(system)
        try:
            lfp2, reports, ck = zpassport.passports(system)
        except Exception as e:                       # noqa: BLE001
            bad += 1
            ex.append((system, "EXC", repr(e)))
            continue
        got = {s: ck[s] for s in names}
        # zpassport records the period in PARADOX's slot only
        if lfp2 != lfp or got != kind:
            bad += 1
            ex.append((system, lfp, kind, lfp2, got))
    rec("passport: lfp / kind / period", n, bad, ex)


SECTIONS = {"eval": (s_eval, 400_000), "exhaustive": (s_exhaustive, 7),
            "classical": (s_classical, 200_000), "grade": (s_grade, 200_000),
            "judge": (s_judge, 100_000), "parse": (s_parse, 200_000),
            "passport": (s_passport, 50_000)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", default="20260927")
    ap.add_argument("--scale", type=float, default=1.0)
    ap.add_argument("--only", default=None)
    ap.add_argument("--json", default=None)
    a = ap.parse_args()
    names = a.only.split(",") if a.only else list(SECTIONS)
    t0 = time.time()
    print(f"seed {a.seed}, scale {a.scale}")
    for s in names:
        fn, n = SECTIONS[s]
        fn(a.seed, n if s == "exhaustive" else max(1, int(n * a.scale)))
    print(f"{time.time() - t0:.0f} s")
    if a.json:
        json.dump(OUT, open(a.json, "w"), indent=1, default=str)



# ------------------------------------------------------------------ laws
def _valid_identity(lhs, rhs, names):
    """lhs = rhs as values, under every T/F/Z valuation of `names`."""
    return all(O.ev(lhs, e) == O.ev(rhs, e)
               for e in (dict(zip(names, c)) for c in product(O.VALS, repeat=len(names))))


def _valid(phi, names, vals=O.VALS):
    return all(O.ev(phi, dict(zip(names, c))) == "T"
               for c in product(vals, repeat=len(names)))


def _entails(prems, concl, names):
    for c in product(O.VALS, repeat=len(names)):
        e = dict(zip(names, c))
        if all(O.ev(pr, e) == "T" for pr in prems) and O.ev(concl, e) != "T":
            return False
    return True


def s_laws(seed, _n):
    """The laws SPEC.md / lean/ZTL.lean state, re-derived from the oracle's
    tables; the rule battery; the pool numbers of CLASSIC-VS-ZTL.md; the
    expressible-function count; the paradox catalogue and the parity law."""
    p, q, r = "p", "q", "r"
    N = lambda x: ("not", x)
    A = lambda x, y: ("and", x, y)
    Or = lambda x, y: ("or", x, y)
    I = lambda x, y: ("imp", x, y)
    X = lambda x, y: ("xor", x, y)
    E = lambda x, y: ("xnor", x, y)
    out, bad = [], []
    # SPEC.md "Extend to the mark (12)" — each must hold on T/F/Z
    extend = {
        "modus ponens (semantic)": ("rule", [p, I(p, q)], q),
        "non-contradiction": ("valid", N(A(p, N(p)))),
        "transitivity of ->": ("rule", [I(p, q), I(q, r)], I(p, r)),
        "comm and": ("id", A(p, q), A(q, p)), "comm or": ("id", Or(p, q), Or(q, p)),
        "assoc and": ("id", A(A(p, q), r), A(p, A(q, r))),
        "assoc or": ("id", Or(Or(p, q), r), Or(p, Or(q, r))),
        "distrib and/or": ("id", A(p, Or(q, r)), Or(A(p, q), A(p, r))),
        "distrib or/and": ("id", Or(p, A(q, r)), A(Or(p, q), Or(p, r))),
        "p->q = ~p|q": ("id", I(p, q), Or(N(p), q)),
        "p^q = (p&~q)|(~p&q)": ("id", X(p, q), Or(A(p, N(q)), A(N(p), q))),
        "p=q = (p&q)|(~p&~q) = (p->q)&(q->p)": ("id2", E(p, q), Or(A(p, q), A(N(p), N(q))),
                                               A(I(p, q), I(q, p))),
    }
    # SPEC.md "Fallen laws (14)" — each must FAIL somewhere on T/F/Z (and
    # hold on T/F: "all 26 hold on verified data")
    fallen = {
        "double negation": ("id", N(N(p)), p),
        "De Morgan 1": ("id", N(A(p, q)), Or(N(p), N(q))),
        "De Morgan 2": ("id", N(Or(p, q)), A(N(p), N(q))),
        "contraposition": ("id", I(p, q), I(N(q), N(p))),
        "xor = ~xnor": ("id", X(p, q), N(E(p, q))),
        "idem and": ("id", A(p, p), p), "idem or": ("id", Or(p, p), p),
        "absorption": ("id", A(p, Or(p, q)), p),
        "unit and": ("id", A(p, "T"), p), "unit or": ("id", Or(p, "F"), p),
        "excluded middle": ("valid", Or(p, N(p))),
        "reflexivity p->p": ("valid", I(p, p)),
        "Peirce": ("valid", I(I(I(p, q), p), p)),
        "q->(p->q)": ("valid", I(q, I(p, q))),
    }

    def holds(spec, vals):
        kind = spec[0]
        names = sorted(set().union(*[O.atoms(x) for x in
                       (spec[1:] if kind != "rule" else spec[1] + [spec[2]])]))
        envs = [dict(zip(names, c)) for c in product(vals, repeat=len(names))]
        if kind == "valid":
            return all(O.ev(spec[1], e) == "T" for e in envs)
        if kind == "id":
            return all(O.ev(spec[1], e) == O.ev(spec[2], e) for e in envs)
        if kind == "id2":
            return all(O.ev(spec[1], e) == O.ev(spec[2], e) == O.ev(spec[3], e) for e in envs)
        return all(O.ev(spec[2], e) == "T" for e in envs
                   if all(O.ev(pr, e) == "T" for pr in spec[1]))
    for name, spec in extend.items():
        ok = holds(spec, O.VALS) and holds(spec, ("T", "F"))
        if not ok:
            bad.append(("extend", name))
    for name, spec in fallen.items():
        ok = (not holds(spec, O.VALS)) and holds(spec, ("T", "F"))
        if not ok:
            bad.append(("fallen", name, "T/F:", holds(spec, ("T", "F")),
                        "T/F/Z:", holds(spec, O.VALS)))
    out.append(f"SPEC laws: {len(extend)} extend, {len(fallen)} fall")
    # SPEC.md keel: 12 of 14 rules survive; the two that fall are named
    rules = {
        "modus ponens": ([p, I(p, q)], q), "modus tollens": ([I(p, q), N(q)], N(p)),
        "contraposition-rule": ([I(p, q)], I(N(q), N(p))),
        "disjunctive syllogism": ([Or(p, q), N(p)], q), "and-intro": ([p, q], A(p, q)),
        "and-elim": ([A(p, q)], p), "or-intro": ([p], Or(p, q)),
        "~~-intro": ([p], N(N(p))), "~~-elim": ([N(N(p))], p),
        "transitivity": ([I(p, q), I(q, r)], I(p, r)), "K-rule": ([q], I(p, q)),
        "tautology in concl.": ([p], Or(q, N(q))), "explosion": ([p, N(p)], q),
        "resolution": ([Or(p, q), Or(N(p), r)], Or(q, r)),
    }
    alive = {k for k, (pr, c) in rules.items()
             if _entails(pr, c, sorted(set().union(*[O.atoms(x) for x in pr + [c]])))}
    dead = set(rules) - alive
    out.append(f"rules alive {len(alive)}, dead {sorted(dead)}")
    if len(alive) != 12 or dead != {"~~-elim", "tautology in concl."}:
        bad.append(("rules", sorted(dead)))
    # deduction theorem one way: p |= p but not |= p -> p
    if not (_entails([p], p, [p]) and not _valid(I(p, p), [p])):
        bad.append("deduction theorem")
    # greediness: no compound ever takes Z (all depth<=3 formulas over p,q)
    comp_z = 0
    for s in range(2, 6):
        for phi in O.all_formulas(s, ["p", "q"]):
            if not isinstance(phi, str):
                for c in product(O.VALS, repeat=2):
                    if O.ev(phi, dict(zip(["p", "q"], c))) == "Z":
                        comp_z += 1
    out.append(f"compounds taking Z (all <=5-node formulas over p,q): {comp_z}")
    if comp_z:
        bad.append(("greediness", comp_z))
    # CLASSIC-VS-ZTL.md / zledger: the depth<=2 pool, rebuilt from its definition
    d0 = ["p", "q"]
    d1 = [N(a) for a in d0] + [(op, a, b) for op in O.OPS for a in d0 for b in d0]
    base = d0 + d1
    d2 = [N(f) for f in d1] + [(op, a, b) for op in O.OPS for a in base for b in base]
    pool = list(dict.fromkeys(d0 + d1 + d2))
    sig = lambda phi, vals: tuple(O.ev(phi, {"p": a, "q": b}) for a in vals for b in vals)
    cl = [f for f in pool if all(v == "T" for v in sig(f, ("T", "F")))]
    one = [f for f in cl if all(O.ev(f, {"p": a, "q": "Z"}) == "T" for a in ("T", "F"))]
    none = [f for f in cl if all(v == "T" for v in sig(f, O.VALS))]
    classes = {}
    for f in pool:
        classes.setdefault(sig(f, ("T", "F")), set()).add(sig(f, O.VALS))
    ztl_classes = {sig(f, O.VALS) for f in pool}
    split = sum(1 for v in classes.values() if len(v) > 1)
    out.append(f"pool {len(pool)} formulas: classical tautologies {len(cl)}, "
               f"with one of two verified {len(one)}, with none {len(none)}; "
               f"classes classical {len(classes)} / ZTL {len(ztl_classes)}, split {split}")
    # expressible binary functions {T,F,Z}^2 -> {T,F,Z}: closure from p, q
    cells = [(a, b) for a in O.VALS for b in O.VALS]
    for label, start in (("from p, q", ["p", "q"]), ("from p, q, T, F", ["p", "q", "T", "F"]),
                         ("from p, q, T, F, Z", ["p", "q", "T", "F", "Z"])):
        funcs = {tuple(O.ev(x, {"p": a, "q": b}) for a, b in cells) for x in start}
        while True:
            new = set(funcs)
            for f in funcs:
                new.add(tuple(O.TABLE1[x] for x in f))
                for g in funcs:
                    for op in O.OPS:
                        new.add(tuple(O.TABLE2[op][(x, y)] for x, y in zip(f, g)))
            if new == funcs:
                break
            funcs = new
        out.append(f"expressible binary functions {label}: {len(funcs)} of {3 ** 9}")
    # the paradox catalogue (zparadox.py header) and the parity law (zpassport)
    cat = {
        "liar": ({"L": N("L")}, "L", ("PARADOX", 2)),
        "truth-teller": ({"t": "t"}, "t", ("UNDERDETERMINED", 2)),
        "carousel": ({"A": "B", "B": N("A")}, "A", ("PARADOX", 4)),
        "even cycle": ({"A": N("B"), "B": N("A")}, "A", ("UNDERDETERMINED", 2)),
        "odd cycle-3": ({"a": N("b"), "b": N("c"), "c": N("a")}, "a", ("PARADOX", 2)),
    }
    for name, (sysm, s, want) in cat.items():
        _, kind = O.passports(sysm)
        _, _, ck = zpassport.passports(sysm)
        if kind[s] != want or ck[s] != want:
            bad.append(("catalogue", name, "oracle", kind[s], "code", ck[s], "doc", want))
    # the header's periods: truth-teller 1, even cycle 2 (greedy)
    for name, sysm, per in (("truth-teller", {"t": "t"}, 1), ("even cycle", {"A": N("B"), "B": N("A")}, 2)):
        c = sorted(sysm)
        if O.greedy_period(c, sysm, {}) != per:
            bad.append(("period", name, O.greedy_period(c, sysm, {}), per))
    par = 0
    for n in range(1, 7):
        for pat in product((0, 1), repeat=n):
            sysm = {f"s{i}": (N(f"s{(i + 1) % n}") if inv else f"s{(i + 1) % n}")
                    for i, inv in enumerate(pat)}
            _, kind = O.passports(sysm)
            want = "PARADOX" if sum(pat) % 2 else "UNDERDETERMINED"
            par += 1
            if kind["s0"][0] != want:
                bad.append(("parity", pat, kind["s0"]))
    out.append(f"parity law on {par} cycles (n<=6)")
    for line in out:
        print("   ", line)
    OUT["laws"] = {"lines": out, "disagreements": bad}
    print(f"  {'laws / rules / counts / catalogue':34s} disagreements {len(bad)}")
    for b in bad:
        print("     ", b)


SECTIONS["laws"] = (s_laws, 1)



def s_joint(seed, n):
    """ztljudge's `joint` and `joint_sets` against their definition: `joint` is
    every unverified ground when no single one (at T or F) moves the verdict or
    the grade; `joint_sets` are the minimal sets that do."""
    from itertools import combinations
    rnd = random.Random(f"joint:{seed}")
    bad, ex, checked, nonempty = 0, [], 0, 0
    for _ in range(n):
        ats = [f"p{j}" for j in range(rnd.randint(2, 5))]
        phi = O.random_formula(rnd, rnd.randint(1, 5), ats, p_const=0.0)
        marks = {a: rnd.choice(["T", "F", "Z"]) for a in ats if rnd.random() < 0.4}
        r = ztljudge.judge(O.text_full(phi), marks)
        if r["disposition"] in ("EARNED", "REFUTED", "E"):
            continue
        checked += 1
        kern = {a: marks.get(a, "Z") for a in O.atoms(phi)}
        unv = sorted(a for a, v in kern.items() if v == "Z")
        base = (O.ev(phi, kern), O.grade(phi, kern))

        def moves(S):
            for vals in product("TF", repeat=len(S)):
                k2 = dict(kern)
                k2.update(zip(S, vals))
                if (O.ev(phi, k2), O.grade(phi, k2)) != base:
                    return True
            return False
        want = [] if len(unv) < 2 or any(moves([a]) for a in unv) else unv
        if r["joint"] != want:
            bad += 1
            ex.append((O.text_full(phi), marks, r["joint"], want))
        if want:
            nonempty += 1
            sets = ztljudge.joint_sets(ztljudge.formalize(O.text_full(phi)), marks)
            mins = []
            for k in range(2, len(unv) + 1):
                for S in combinations(unv, k):
                    if any(set(m) < set(S) for m in mins):
                        continue
                    if moves(list(S)):
                        mins.append(S)
            if sorted(map(tuple, sets)) != sorted(mins):
                bad += 1
                ex.append(("sets", O.text_full(phi), marks, sets, mins))
    rec(f"joint / joint_sets ({nonempty} non-empty)", checked, bad, ex)


def s_stip(seed, n):
    """zpassport.stipulation_theorem on random systems: every classical model
    of an UNDERDETERMINED / INTRINSIC component grounds it cleanly; every
    decree on a PARADOX component contradicts a definition."""
    rnd = random.Random(f"stip:{seed}")
    bad, ex = 0, []
    for _ in range(n):
        names = [f"s{j}" for j in range(rnd.randint(1, 4))]
        system = {s: O.random_formula(rnd, rnd.randint(0, 3), names, p_const=0.0)
                  for s in names}
        ou, cu, op_, cp = zpassport.stipulation_theorem(system)
        if ou != cu or op_ != cp:
            bad += 1
            ex.append((system, ou, cu, op_, cp))
    rec("stipulation theorem", n, bad, ex)


SECTIONS["joint"] = (s_joint, 4000)
SECTIONS["stipulation"] = (s_stip, 3000)


if __name__ == "__main__":
    main()
