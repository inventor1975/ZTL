# -*- coding: utf-8 -*-
"""paper_numbers — the numbers of ZTL-core-logic.tex that core_logic_checks.py does not assert.

core_logic_checks.py recomputes the matrix facts but does not read the paper, and several numbers the
paper quotes were stated in its docstring without a check behind them (the 584 distinct validities,
the 1098/742 split, the clones, the order-of-birth counts). This script asserts each of them, reusing
core_logic_checks.py's definitions, then runs the dirty census of the ZTL book and checks its numbers.
Last, it reads the .tex and fails if a number this script owns is missing from the text, so the two
cannot drift apart silently.

Run:  python3 publications/core-logic/paper_numbers.py   (from the ZTL repository root)
      exit 0 = every number reproduced, and present in the paper text where the text is available.

The paper text is not in this repository until the paper is published. It is looked for in $ZTL_PAPER_DIR,
then next to this file, then in the authors' private checkout; if it is not found, the checks that READ the
text (sections I, G, O) are skipped and say so, and every number is still recomputed.
"""
import contextlib
import io
import itertools
import os
import re
import runpy
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZTL = os.path.abspath(os.path.join(HERE, "..", ".."))                     # the ZTL repository root
CORE = os.path.join(ZTL, "publications", "ztl", "core_logic_checks.py")
PAPER = next((os.path.abspath(d) for d in (os.environ.get("ZTL_PAPER_DIR", ""), HERE,
              os.path.join(ZTL, "..", "ztl-private", "publications", "core-logic"))
              if d and os.path.exists(os.path.join(d, "v7", "v7-draft.md"))), None)
with contextlib.redirect_stdout(io.StringIO()):
    C = runpy.run_path(CORE)
if C["failures"]:
    sys.exit(f"core_logic_checks.py is not green: {C['failures']}")
T, F, Z, V = C["T"], C["F"], C["Z"], C["V"]
OPS, CL, SUB, BIN = C["OPS"], C["CL"], C["SUB"], C["BIN"]
ev, POOL, COMPOUNDS = C["ev"], C["POOL"], C["COMPOUNDS"]
ENVS, GENVS = C["ENVS"], C["GENVS"]
failures = []
owned = []          # (number as printed in the paper, what it is)


def check(cond, msg, *numbers):
    print(("  ✓ " if cond else "  ✗ ") + msg)
    if not cond:
        failures.append(msg)
    owned.extend(numbers)


def show(phi):
    return C["show"](phi)


print("A. the regression pool: entries and distinct formulas")
distinct = {show(f) for f in POOL}
check(len(POOL) == 2926 and len(distinct) == 2906, f"pool: {len(POOL)} entries, {len(distinct)} distinct",
      "2\\,906")
zv = [f for f in POOL if all(ev(OPS, f, e) == T for e in GENVS)]
cv = [f for f in POOL if all(ev(CL, f, e) == T for e in GENVS)]
check(len(zv) == len(cv) == 588, f"clean valuations: ZTL {len(zv)} and classical {len(cv)} valid entries")
zs, cs = {show(f) for f in zv}, {show(f) for f in cv}
check(zs == cs and len(zs) == 584, f"as sets: {len(zs)} and {len(cs)} distinct, equal: {zs == cs}", "584")

print("B. mark-sensitive compounds (distinct formulas): the split")
refuse_only = assert_once = 0
seen = set()
for f in COMPOUNDS:
    if show(f) in seen:
        continue
    seen.add(show(f))
    diff = [(ev(OPS, f, e), ev(CL, f, {k: (F if v == Z else v) for k, v in e.items()})) for e in ENVS]
    diff = [(z, s) for z, s in diff if z != s]
    if not diff:
        continue
    if all(z == F and s == T for z, s in diff):
        refuse_only += 1
    else:
        assert_once += 1
check(len(seen) == 2904, f"distinct compounds {len(seen)}", "2\\,904")
check(refuse_only + assert_once == 1830, f"mark-sensitive {refuse_only + assert_once}", "1\\,830")
check(refuse_only == 1088 and assert_once == 742,
      f"only refusing where the substitution asserts: {refuse_only}; at least once asserting: {assert_once}",
      "1\\,088", "742")
check(round(100 * 1830 / 2904) == 63, "63% of the distinct compounds", "63\\%")

print("C. binary clones (functions V x V -> V generated from the projections)")


def clone(ops_bin, op_not):
    cells = [(a, b) for a in V for b in V]
    proj = {tuple(a for a, b in cells), tuple(b for a, b in cells)}
    seen, frontier = set(proj), set(proj)
    while frontier:
        new = set()
        for f in frontier:
            g = tuple(op_not(x) for x in f)
            if g not in seen:
                new.add(g)
            for h in seen | new:
                for op in ops_bin:
                    for u, w in ((f, h), (h, f)):
                        k = tuple(op(x, y) for x, y in zip(u, w))
                        if k not in seen and k not in new:
                            new.add(k)
        seen |= new
        frontier = new
    return len(seen)


zc = clone([OPS[k] for k in BIN], OPS["not"])
sc = clone([SUB[k] for k in BIN], SUB["not"])
check(zc == 2 + 512, f"ZTL binary clone: {zc} = 2 + 512 (every function into {{T,F}})", "512")
check(sc == 2 + 16, f"the substitution's binary clone: {sc} = 2 + 16", "16")

print("D. the default's validities over the pool, marked valuations admitted")
sv = {show(f) for f in POOL if all(ev(SUB, f, e) == T for e in ENVS)}
bv = {show(f) for f in POOL if all(ev(C["BOCH"], f, e) == T for e in ENVS)}
tv_ = {show(f) for f in POOL if all(ev(OPS, f, e) == T for e in ENVS)}
check(len(sv) == 584, f"dirty := false validates {len(sv)} distinct formulas", "584")
check(len(bv) == 548 and len(tv_) == 212 and tv_ < bv and len(bv - tv_) == 336,
      f"distinct validities: external Bochvar {len(bv)}, ZTL {len(tv_)}, a proper subset, difference {len(bv - tv_)}",
      "548", "212", "336")


print("H. Bochvar's external connectives, both conventions; the default; clones")
tv = C["tv"]
box = {T: 1, F: 0, Z: 0}
EXT = {"and": lambda a, b: tv(box[a] and box[b]), "or": lambda a, b: tv(box[a] or box[b]),
       "imp": lambda a, b: tv((not box[a]) or box[b]), "xnor": lambda a, b: tv(box[a] == box[b]),
       "xor": lambda a, b: tv(box[a] != box[b])}
J0 = dict(EXT, **{"not": lambda a: tv(a == F)})
KT = dict(EXT, **{"not": lambda a: tv(not box[a])})
cells = lambda M, N: ([("not", a) for a in V if M["not"](a) != N["not"](a)] +
                      [(k, a, b) for k in BIN for a in V for b in V if M[k](a, b) != N[k](a, b)])
check(cells(SUB, KT) == [], "dirty := false = Karpenko-Tomova external connectives, all 48 cells")
check([c for c in cells(SUB, J0) if c[0] != "not"] == [] and len(cells(SUB, J0)) == 1,
      "dirty := false vs J0 convention: 0 of 45 binary cells, differ only at negation")
check(len(cells(OPS, J0)) == 7 and len(cells(OPS, KT)) == 8, f"ZTL vs J0: {len(cells(OPS, J0))} cells, vs KT: {len(cells(OPS, KT))}")
vJ = {show(f) for f in POOL if all(ev(J0, f, e) == T for e in ENVS)}
vK = {show(f) for f in POOL if all(ev(KT, f, e) == T for e in ENVS)}
check(len(vJ) == 548 and len(vK) == 584, f"validities over all valuations: J0 {len(vJ)}, KT {len(vK)}")
for nm, M, row, dne in (("ZTL", OPS, "FFTFFF", False), ("J0", J0, "FFTTTF", False), ("KT", KT, "TFTTTF", True)):
    got = "".join([M["not"](Z), M["and"](Z, F), M["or"](Z, T), M["imp"](Z, F), M["imp"](Z, Z), M["imp"](T, Z)])
    d = all(M["not"](M["not"](a)) != T or a == T for a in V)
    inv = all(M["not"](M["not"](a)) == a for a in V)
    check(got == row and d == dne and not inv, f"kin row {nm}: {got}, involutive {inv}, rule ¬¬p⊨p {d}")
jc = clone([J0[k] for k in BIN], J0["not"])
check(jc == 514, f"J0 convention binary clone: {jc}")

print("I. Table tab:all against the lift (parsed from the paper)")
import itertools as _it
sbs = {T: [1], F: [0], Z: [1, 0]}
TEX = open(os.path.join(PAPER, "ZTL-core-logic.tex"), encoding="utf-8").read() if PAPER else ""
if not PAPER:
    print("  - SKIP: the paper text is not available here")
_e = TEX.find("label{tab:all}"); blk = TEX[TEX.rfind("\\begin{table}", 0, _e):_e] if PAPER else ""
toks = re.findall(r"\$([^$]*)\$", blk)
rows = [(toks[k], "".join(toks[k + 1:k + 4])) for k in range(len(toks)) if re.fullmatch(r"[01]{4}", toks[k])]
n = 0
for core, rest in rows:
    vals = re.findall(r"\\(T|F)", rest)
    f = {(1, 1): core[0] == "1", (1, 0): core[1] == "1", (0, 1): core[2] == "1", (0, 0): core[3] == "1"}
    want = [lift_ for a in V for b in V for lift_ in [T if all(f[(x, y)] for x in sbs[a] for y in sbs[b]) else F]]
    check(vals == want, f"tab:all row {core}")
    n += 1
check(n == 16 or not PAPER, f"tab:all has {n} binary rows")

print("J. strong Kleene: the reading semantics, the census, the over-grant share")
import itertools as _it2
SB = {T: {1}, F: {0}, Z: {0, 1}}
CLB = {"not": lambda a: 1 - a, "and": lambda a, b: a & b, "or": lambda a, b: a | b,
       "imp": lambda a, b: (1 - a) | b, "xor": lambda a, b: a ^ b, "xnor": lambda a, b: 1 - (a ^ b)}
def kv(f, e):
    if isinstance(f, str):
        return SB[e[f]]
    if f[0] == "not":
        return {1 - a for a in kv(f[1], e)}
    A_, B_ = kv(f[1], e), kv(f[2], e)
    return {CLB[f[0]](a, b) for a in A_ for b in B_}
def occ(phi, e):
    leaves = []
    def walk(f):
        if isinstance(f, str):
            leaves.append(f)
        else:
            for x in f[1:]:
                walk(x)
    walk(phi)
    out = set()
    for r in _it2.product(*[sorted(SB[e[x]]) for x in leaves]):
        it = iter(r)
        def go(f):
            if isinstance(f, str):
                return next(it)
            if f[0] == "not":
                return 1 - go(f[1])
            a = go(f[1]); b = go(f[2]); return CLB[f[0]](a, b)
        out.add(go(phi))
    return out
check(all(occ(f, e) == kv(f, e) for f in POOL for e in ENVS), "readings = strong Kleene on every pool cell (Theorem kleene, instance)")
toK = lambda s_: T if s_ == {1} else F if s_ == {0} else Z
kc = [(k, a, b) for k in BIN for a in V for b in V if toK({CLB[k](x, y) for x in SB[a] for y in SB[b]}) != OPS[k](a, b)]
kc += [("not", a) for a in V if toK({1 - x for x in SB[a]}) != OPS["not"](a)]
check(len(kc) == 20, f"ZTL vs strong Kleene: {len(kc)} of 48 cells", "20")
seen_, zT, over_ = set(), 0, 0
for f in COMPOUNDS:
    if show(f) in seen_:
        continue
    seen_.add(show(f))
    for e in ENVS:
        if Z in e.values() and ev(OPS, f, e) == T:
            zT += 1
            over_ += kv(f, e) != {1}
check(zT == 6186 and over_ == 3738 and round(100 * over_ / zT) == 60,
      f"T on dirty valuations: {zT}, not earned: {over_}", "6\\,186", "3\\,738", "60\\%")

# Lukasiewicz and weak Kleene against the reading semantics
U_ = Z
h_ = {T: 1.0, F: 0.0, Z: 0.5}; bk_ = {1.0: T, 0.0: F, 0.5: Z}
L3 = {"not": lambda a: bk_[1 - h_[a]], "and": lambda a, b: bk_[min(h_[a], h_[b])],
      "or": lambda a, b: bk_[max(h_[a], h_[b])], "imp": lambda a, b: bk_[min(1.0, 1 - h_[a] + h_[b])]}
WK = {k: (lambda k: (lambda *xs: Z if Z in xs else toK({CLB[k](*[1 if x == T else 0 for x in xs])})))(k)
      for k in ("not", "and", "or", "imp")}
def kdiff(M):
    d = [("not", a) for a in V if M["not"](a) != toK({1 - x for x in SB[a]})]
    d += [(k, a, b) for k in ("and", "or", "imp") for a in V for b in V
          if M[k](a, b) != toK({CLB[k](x, y) for x in SB[a] for y in SB[b]})]
    return d
check(kdiff(L3) == [("imp", Z, Z)], f"Lukasiewicz vs readings: {kdiff(L3)}")
check(len(kdiff(WK)) == 6, f"weak Kleene vs readings: {len(kdiff(WK))} cells")
# the census in strong Kleene
KOPS = {"not": lambda a: toK({1 - x for x in SB[a]})}
for k in BIN:
    KOPS[k] = (lambda k: lambda a, b: toK({CLB[k](x, y) for x in SB[a] for y in SB[b]}))(k)
src_ = open(CORE, encoding="utf-8").read()
ns_ = {"N": KOPS["not"], "A": KOPS["and"], "O": KOPS["or"], "I": KOPS["imp"], "X": KOPS["xor"], "E": KOPS["xnor"],
       "T": T, "F": F, "Z": Z}
exec(src_[src_.index("LAWS_KEEP = {"):src_.index("def ground_law_holds")], ns_)
V3_ = list(_it2.product(V, repeat=3))
keep_ = sum(all(l(*t) for t in V3_) for l in ns_["LAWS_KEEP"].values())
ids_ = sum(all(f(*t)[0] == f(*t)[1] for t in V3_) for f, isf in ns_["LAWS_GROUND"].values() if not isf)
undec_ = sum({f(*t)[0] for t in V3_} == {T, Z} for f, isf in ns_["LAWS_GROUND"].values() if isf)
nc_ = all(ns_["LAWS_KEEP"]["non-contradiction"](*t) for t in V3_)
check(keep_ == 11 and ids_ == 10 and undec_ == 4 and not nc_,
      f"strong Kleene on the census: {keep_} of 12 kept, {ids_} of 10 identities hold, {undec_} formulas undecided; total {keep_ + ids_}", "21")

print("K. dominance of the earned verdict (regression pool, dirty cells)")
def refs_(e):
    ks = [k for k in e if e[k] == Z]
    for vals in _it2.product((Z, T, F), repeat=len(ks)):
        d = dict(e); d.update(zip(ks, vals)); yield d
seen2, cells2 = set(), 0
J = {T: [0, 0], F: [0, 0]}; M_ = {T: [0, 0], F: [0, 0]}; viol = 0
for f in POOL:
    if show(f) in seen2:
        continue
    seen2.add(show(f))
    for e in ENVS:
        if Z not in e.values():
            continue
        cells2 += 1
        k3T = kv(f, e) == {1}
        E_ = all(ev(OPS, f, d) == T for d in refs_(e))
        viol += (k3T and not E_)
        for x in (T, F):
            dg = ev(CL, f, {k: (x if v == Z else v) for k, v in e.items()}) == T
            viol += (E_ and not dg)
            for box, g in ((J, E_), (M_, ev(OPS, f, e) == T)):
                if (g == k3T) and not (dg == k3T): box[x][0] += 1
                if (dg == k3T) and not (g == k3T): box[x][1] += 1
check(cells2 == 14530 and viol == 0, f"{cells2} dirty cells; theorem-instance violations: {viol}", "14\\,530")
check(J[F] == [4408, 0] and J[T] == [5638, 0], f"judge vs defaults: false {J[F]}, true {J[T]}", "4\\,408", "5\\,638")
check(M_[F][1] == 1458 and M_[T][1] == 1606, f"matrix alone, reverse counts: {M_[F][1]}, {M_[T][1]}", "1\\,458", "1\\,606")

print("L. ZTL against classical logic about the world (certain answers over completions), dirty cells")
seen3, both_, zonly, conly = set(), 0, 0, 0
for f in COMPOUNDS:
    if show(f) in seen3:
        continue
    seen3.add(show(f))
    for e in ENVS:
        if Z not in e.values():
            continue
        comps = [{k: (x if e[k] == Z else e[k]) for k, x in zip(e, vals)} for vals in _it2.product((T, F), repeat=len(e))]
        clT = all(ev(CL, f, c) == T for c in comps)
        zT = ev(OPS, f, e) == T
        both_ += clT and zT; zonly += zT and not clT; conly += clT and not zT
check(zonly == 2744 and conly == 1446, f"ZTL-only {zonly}, classical-only {conly}, both {both_}", "2\\,744", "1\\,446")
seedsrc = open(os.path.join(ZTL, "publications", "book", "checks", "dirty_census.py"), encoding="utf-8").read()
check("random.Random(20261025)" in seedsrc, "the random sample's seed in dirty_census.py", "20261025")

print("E. order of birth: one atom, pure doubt")
d1c = [("not", "p")] + [(o, "p", "p") for o in BIN]
d1 = ["p"] + d1c
d2 = [("not", x) for x in d1c] + [(o, a, b) for o in BIN for a in d1 for b in d1 if not (a == "p" and b == "p")]
doubt = {"p": Z}
t1 = sum(ev(OPS, f, doubt) == T for f in d1c)
t2 = [f for f in d2 if ev(OPS, f, doubt) == T]
check(len(d1c) == 6 and t1 == 0, f"depth 1: {t1} of {len(d1c)} take T", "6")
check(len(d1c) + len(d2) == 252 and len(d2) == 246 and len(t2) == 84,
      f"depth <= 2: {len(t2)} of {len(d1c) + len(d2)} take T, all at depth exactly 2 ({len(t2)} of {len(d2)})",
      "84", "252", "246")


def subs(f):
    if isinstance(f, str):
        return []
    return [s for a in f[1:] for s in [a] + subs(a)]


check(all(any(ev(OPS, s, doubt) == F for s in subs(f)) for f in t2), "each of the 84 has a false proper subformula")

print("F. the dirty census (ZTL book check, run now)")
out = subprocess.run([sys.executable, os.path.join(ZTL, "publications", "book", "checks", "dirty_census.py")],
                     capture_output=True, text=True, timeout=3600).stdout
want = {"marked cells                         248121": "248\\,121", "LOSS vs dirty (P1 requires 0)        0": None,
        "loss vs patient (old 'losses')       14844": "14\\,844", "leak vs patient (old 'leaks')        44847": "44\\,847",
        "leak vs dirty                        55176": "55\\,176", "marked cells                         15295": None,
        "skipped (>14 dirty occurrences)      740": "740", "P1 HOLDS": None}
check(15295 - 740 == 14555, "random pool: 15295 marked cells, 740 skipped, 14555 checked", "14\\,555")
check(55176 - 44847 == 10329, "over-grants no cleaning overturns: 55176 - 44847 = 10329", "10\\,329")
for line, num in want.items():
    check(line in out, f"dirty census: {line.split('  ')[0].strip()} -> {line.split()[-1]}", *([num] if num else []))

print("N. v7 additions (2026-10-29): the Kleene clone, the KT clone, Kleene's laws by decision")
kc = clone([KOPS[k] for k in BIN], KOPS["not"])
_bx = {T: 1, F: 0, Z: 0}     # its own copy: section J rebinds the global name `box`, and KT's lambdas read it late
_KT2 = {"and": lambda a, b: tv(_bx[a] and _bx[b]), "or": lambda a, b: tv(_bx[a] or _bx[b]),
        "imp": lambda a, b: tv((not _bx[a]) or _bx[b]), "xnor": lambda a, b: tv(_bx[a] == _bx[b]),
        "xor": lambda a, b: tv(_bx[a] != _bx[b]), "not": lambda a: tv(not _bx[a])}
ktc = clone([_KT2[k] for k in BIN], _KT2["not"])
check(kc == 82, f"strong Kleene binary clone: {kc}")
check(ktc == 18, f"Bochvar external, 'not true' convention, binary clone: {ktc} = 2 + 16")
_N, _A, _O, _I, _X, _E = (KOPS[k] for k in ("not", "and", "or", "imp", "xor", "xnor"))
SIDES = {   # the nineteen identities of the census, both sides, in strong Kleene
    "and comm": lambda p, q, r: (_A(p, q), _A(q, p)), "or comm": lambda p, q, r: (_O(p, q), _O(q, p)),
    "and assoc": lambda p, q, r: (_A(_A(p, q), r), _A(p, _A(q, r))),
    "or assoc": lambda p, q, r: (_O(_O(p, q), r), _O(p, _O(q, r))),
    "and over or": lambda p, q, r: (_A(p, _O(q, r)), _O(_A(p, q), _A(p, r))),
    "or over and": lambda p, q, r: (_O(p, _A(q, r)), _A(_O(p, q), _O(p, r))),
    "imp def": lambda p, q, r: (_I(p, q), _O(_N(p), q)),
    "xor def": lambda p, q, r: (_X(p, q), _O(_A(p, _N(q)), _A(_N(p), q))),
    "xnor def": lambda p, q, r: (_E(p, q), _O(_A(p, q), _A(_N(p), _N(q)))),
}
for nm, (f, isf) in ns_["LAWS_GROUND"].items():
    if not isf:
        SIDES[nm] = f
# the atoms a law is WRITTEN over (p = 0, q = 1, r = 2), not the ones its sides happen to depend on: in absorption
# p ∧ (p ∨ q) = p the sides do not depend on q, yet a valuation with q dirty and p true tests the law, and there it
# holds by decided values (T = T). Counting by dependence gave nine; by the written atoms, eight.
_ARITY = {"and assoc": 3, "or assoc": 3, "and over or": 3, "or over and": 3,
          "¬¬p=p": 1, "∧ idem": 1, "∨ idem": 1, "p∧T=p": 1, "p∨F=p": 1}
def _used(nm):
    return list(range(_ARITY.get(nm, 2)))
only_u, some_u = [], 0
for nm, f in SIDES.items():
    used = _used(nm)
    dirty = [t for t in V3_ if any(t[k] == Z for k in used)]
    holds = all(f(*t)[0] == f(*t)[1] for t in V3_)
    decided = [t for t in dirty if f(*t)[0] == f(*t)[1] != Z]
    both_u = [t for t in dirty if f(*t)[0] == f(*t)[1] == Z]
    assert holds, nm
    some_u += bool(both_u)
    if not decided:
        only_u.append(nm)
check(len(SIDES) == 19 and some_u == 19 and len(only_u) == 8,
      f"strong Kleene identities: {len(SIDES)} hold; {some_u} rely on u = u in some dirty cell; {len(only_u)} only on it "
      f"({', '.join(sorted(only_u))})")

print("P. the judge's dispositions against strong Kleene (v7 §5), dirty cells of the distinct pool")
sys.path.insert(0, ZTL)
import ztljudge as _J                                                    # noqa: E402
_seen, _disp, _dom = set(), {}, {F: [0, 0], T: [0, 0]}   # per default d: [judge right & d wrong, the reverse]
for f in POOL:
    key = show(f)
    if key in _seen:
        continue
    _seen.add(key)
    phi = _J.formalize(_J._show(f)) if not isinstance(f, str) else f
    for e in ENVS:
        if Z not in e.values():
            continue
        k = kv(f, e)
        kk = "T" if k == {1} else "F" if k == {0} else "U"
        d = _J.judge(_J._show(phi), dict(e))["disposition"]
        _disp[(d, kk)] = _disp.get((d, kk), 0) + 1
        right, grant = kk == "T", d in ("EARNED", "EARNED IF STABLE")
        for dflt in (F, T):
            sg = ev(CL, f, {a: (dflt if x == Z else x) for a, x in e.items()}) == T
            _dom[dflt][0] += grant == right and sg != right
            _dom[dflt][1] += sg == right and grant != right
_exp = {("EARNED", "T"): 2450, ("REFUTED", "F"): 1274, ("EARNED IF STABLE", "U"): 2440,   # IF STABLE by completions
        ("REFUTED IF STABLE", "U"): 1470, ("ON CREDIT", "U"): 2296, ("OPEN", "U"): 4600}  # since 2026-10-29 evening
check(_disp == _exp, f"judge vs strong Kleene: {dict(sorted(_disp.items()))}")
check(_dom == {F: [2918, 0], T: [4148, 0]},
      f"judge's grant vs the uniform defaults (right / the default wrong, and the reverse): {_dom}")  # preprint 2.1.6 §10   # quoted in v7 §5 (section O)

print("G. every number this script owns appears in the paper")
if not PAPER:
    print("  - SKIP: the paper text is not available here")
tex = open(os.path.join(PAPER, "ZTL-core-logic.tex"), encoding="utf-8").read() if PAPER else None
NOT_QUOTED = {"10\\,329", "14\\,530", "14\\,555", "14\\,844", "1\\,088", "1\\,458", "1\\,606", "1\\,830", "246",
              "248\\,121", "252", "2\\,904", "336", "44\\,847", "4\\,408", "512", "548", "55\\,176", "5\\,638", "63\\%",
              "740", "742", "84", "20261025"}   # recomputed above, not quoted in the v4 text (2026-10-28 rewrite)
for n in (sorted(set(owned) - NOT_QUOTED) if PAPER else []):
    pat = re.escape(n).replace("\\\\,", "(?:\\\\,|,|)")
    check(re.search(r"(?<![\d.])" + pat + r"(?![\d])", tex) is not None, f"in the text: {n}")

print("O. the numbers of the v7 draft owned here appear in v7/v7-draft.md")
if not PAPER:
    print("  - SKIP: the paper text is not available here")
V7 = open(os.path.join(PAPER, "v7", "v7-draft.md"), encoding="utf-8").read() if PAPER else ""
for n in () if not PAPER else ("82 binary functions", "514", "only 18 binary functions", "eight of them only",
          "twenty-one of the twenty-six", "EARNED 2 450", "REFUTED 1 274"):
    # The v7 §5 counts of the four IF STABLE / ON CREDIT / OPEN dispositions went stale when IF STABLE moved to
    # completions (2026-10-29 evening); the article is paused (curator) and §5 is to be rewritten — section P above
    # holds the current numbers.
    check(n in V7, f"in the v7 draft: {n}")

print()
if failures:
    print(f"PAPER NUMBERS RED — {len(failures)} failure(s)")
    sys.exit(1)
print("PAPER NUMBERS GREEN" + ("" if PAPER else " (numbers only: the paper text was not available, sections I, G, O skipped)"))
