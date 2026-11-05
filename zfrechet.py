# -*- coding: utf-8 -*-
"""
zfrechet — truth degrees with a dirty dependence: does interval (Fréchet) logic extend ZTL without moving a verdict?

The curator, 2026-11-05: "как в фазовой (fuzzy) логике — A и B при 0.3 и 0.7 дают 0.3, A или B — 0.7 … перебрал OR,
NAND, IMPL, и вроде работает с грязным параметром". The correction agreed the same evening: min/max are not the
probability of "A and B" — that depends on how A and B are joined, which nobody gave. The honest answer is the
interval over every joint (Boole, Fréchet): P(A and B) in [max(0, a+b-1), min(a, b)]. The unknown joint IS the dirty
parameter; independence is a stipulation that narrows it to a point. Fuzzy min/max is one END of that interval: the
silent assumption that A and B are as joined as they can be.

THE EMBEDDING, IN WORDS FIRST. A truth degree is an interval [lo, hi] in [0, 1]: T = [1, 1], F = [0, 0], Z = [0, 1].
A formula's degree is the range of P(formula) over every joint distribution of its events that keeps each event's own
degree. Which occurrences are ONE event is the dirty rule (canon 25.10): a clean atom is one fact wherever it occurs;
a dirty atom may be read differently at each occurrence (its owner can change it between two reads), so each
occurrence is its own event — unless stability is ASSUMED (the judge's "IF STABLE"), when the occurrences co-refer.

MEASURED HERE (each section asserts what it prints):
  1. the 16 binary connectives on {T, F, Z}: the projection "T iff lo = 1, else F" of the interval output equals
     ZTL's lifted table (ztl.lift2: T only if forced under every classical reading) — 16 x 9 cells;
  2. formulas: random formulas over 3 atoms, every marking in {T, F, Z}^3: the interval with separate reads gives
     EARNED exactly when lo = 1 and REFUTED exactly when hi = 0; with co-referring reads, EARNED IF STABLE /
     REFUTED IF STABLE — against ztljudge.judge, every formula, every marking;
  3. fractional degrees, the curator's 0.3 and 0.7: the Fréchet interval of each connective, exactly (the joint of
     two events is one number p11, and every connective's probability is linear in it, so the ends are exact); the
     fuzzy min/max value is an END of the interval for and/or/nand/nor/imp, and lies inside for xor/xnor;
  4. clean against dirty on one atom of degree 0.3: A and not-A is [0, 0] when A is one fact, [0, 0.3] when each
     occurrence is its own read; A or not-A is [1, 1] against [0.7, 1]; independence, stipulated, gives a point inside
     every interval of section 3.
WHAT THIS IS NOT: a new probability theory (Boole 1854, Fréchet 1935, Hailperin; Walley's imprecise probabilities).
What is checked is that it sits on ZTL with no verdict moved.

Run:  python3 zfrechet.py
"""
import itertools
import random
from fractions import Fraction as Fr

from ztl import T, F, Z, lift2
from ztljudge import judge, formalize

ONE, ZERO = Fr(1), Fr(0)


# ------------------------------------------------------------------ 1. the 16 binary connectives
def table(bits):
    """bits = (f(F,F), f(F,T), f(T,F), f(T,T)) in {0,1}"""
    return lambda x, y: bits[2 * x + y]


def interval_out(f, a, b):
    """[lo, hi] of P(f(A,B)) over every joint of events A, B with P(A) in a, P(B) in b (a, b intervals)"""
    vals = []
    for pa in (a[0], a[1]):
        for pb in (b[0], b[1]):
            lo11, hi11 = max(ZERO, pa + pb - 1), min(pa, pb)
            for p11 in (lo11, hi11):                       # P(f) is linear in p11: the ends are exact
                p10, p01 = pa - p11, pb - p11
                p00 = 1 - p11 - p10 - p01
                vals.append(p11 * f(1, 1) + p10 * f(1, 0) + p01 * f(0, 1) + p00 * f(0, 0))
    return (min(vals), max(vals))


DEG = {T: (ONE, ONE), F: (ZERO, ZERO), Z: (ZERO, ONE)}


def project(iv):
    return T if iv[0] == 1 else F                           # ZTL's connectives: T only if forced


def sec1_sixteen():
    print("-" * 72)
    print("1. THE 16 BINARY CONNECTIVES ON {T, F, Z}: THE PROJECTION IS ZTL'S TABLE")
    cells = bad = 0
    for bits in itertools.product((0, 1), repeat=4):
        f = table(bits)
        lifted = lift2(lambda x, y, f=f: T if f(1 if x == T else 0, 1 if y == T else 0) else F)
        for x in (T, F, Z):
            for y in (T, F, Z):
                cells += 1
                # the lift reads EACH ARGUMENT as given (an occurrence of its own): separate events, so the joint
                # of two Z arguments is free — exactly the interval's 'every joint'
                if project(interval_out(f, DEG[x], DEG[y])) != lifted(x, y):
                    bad += 1
    assert (cells, bad) == (144, 0), (cells, bad)
    print(f"   {cells} cells, {bad} differ: interval logic projected = ZTL's lifted connectives")


# ------------------------------------------------------------------ 2. formulas against the judge
def worlds_value(phi, assign):
    """classical value of phi (ztl tuple syntax) under a 0/1 assignment of its EVENTS (names)"""
    if isinstance(phi, str):
        return assign[phi]
    op = phi[0]
    if op == "not":
        return 1 - worlds_value(phi[1], assign)
    a, b = worlds_value(phi[1], assign), worlds_value(phi[2], assign)
    return {"and": a & b, "or": a | b, "imp": (1 - a) | b, "xor": a ^ b, "xnor": 1 - (a ^ b)}[op]


def split_occurrences(phi, dirty, counter):
    """rename every occurrence of a dirty atom apart (each read is its own event)"""
    if isinstance(phi, str):
        if phi in dirty:
            counter[phi] = counter.get(phi, 0) + 1
            return f"{phi}#{counter[phi]}"
        return phi
    return (phi[0],) + tuple(split_occurrences(p, dirty, counter) for p in phi[1:])


def events(phi, acc=None):
    acc = set() if acc is None else acc
    if isinstance(phi, str):
        acc.add(phi)
    else:
        for p in phi[1:]:
            events(p, acc)
    return acc


def degree_01(phi, marking, separate):
    """[lo, hi] when every degree is T, F or Z: Z events range freely, T/F are fixed — so lo = 1 iff phi holds in
    every world the fixed events allow, hi = 0 iff it fails in every one (exact, by enumeration)"""
    dirty = {a for a, v in marking.items() if v == "Z"}
    psi = split_occurrences(phi, dirty, {}) if separate else phi
    evs = sorted(events(psi))
    free = [e for e in evs if marking[e.split("#")[0]] == "Z"]
    fixed = {e: (1 if marking[e.split("#")[0]] == "T" else 0) for e in evs if e not in free}
    seen = {worlds_value(psi, {**fixed, **dict(zip(free, bits))}) for bits in itertools.product((0, 1), repeat=len(free))}
    return (ONE if seen == {1} else ZERO, ZERO if seen == {0} else ONE)


def rand_formula(rng, names, d):
    if d == 0 or rng.random() < .3:
        return rng.choice(names)
    op = rng.choice(["and", "or", "imp", "xor", "xnor", "not"])
    if op == "not":
        return ("not", rand_formula(rng, names, d - 1))
    return (op, rand_formula(rng, names, d - 1), rand_formula(rng, names, d - 1))


def text(phi):
    if isinstance(phi, str):
        return phi
    if phi[0] == "not":
        return f"~({text(phi[1])})"
    sym = {"and": "&", "or": "|", "imp": "->", "xor": "^", "xnor": "="}[phi[0]]
    return f"({text(phi[1])} {sym} {text(phi[2])})"


def sec2_formulas(n=400):
    print("-" * 72)
    print("2. FORMULAS: THE INTERVAL WITH SEPARATE / CO-REFERRING READS AGAINST THE JUDGE")
    rng = random.Random(25)
    names = ["a", "b", "c"]
    checked = 0
    for _ in range(n):
        phi = rand_formula(rng, names, 4)
        src = text(phi)
        assert formalize(src) is not None
        for vals in itertools.product("TFZ", repeat=3):
            marking = dict(zip(names, vals))
            d = judge(src, marking)["disposition"]
            sep, co = degree_01(phi, marking, True), degree_01(phi, marking, False)
            want = ("EARNED" if sep[0] == 1 else "REFUTED" if sep[1] == 0
                    else "EARNED IF STABLE" if co[0] == 1 else "REFUTED IF STABLE" if co[1] == 0 else "OTHER")
            got = d if d in ("EARNED", "REFUTED", "EARNED IF STABLE", "REFUTED IF STABLE") else "OTHER"
            assert want == got, (src, marking, sep, co, d)
            checked += 1
    print(f"   {n} random formulas x 27 markings = {checked} judgments: EARNED <=> lo = 1 (separate reads),")
    print("   REFUTED <=> hi = 0; IF STABLE <=> the same with co-referring reads — no difference anywhere")


# ------------------------------------------------------------------ 3. fractional degrees
CONN = {"and": (0, 0, 0, 1), "or": (0, 1, 1, 1), "nand": (1, 1, 1, 0), "nor": (1, 0, 0, 0),
        "imp": (1, 1, 0, 1), "xor": (0, 1, 1, 0), "xnor": (1, 0, 0, 1)}
FUZZY = {"and": min, "or": max, "nand": lambda a, b: 1 - min(a, b), "nor": lambda a, b: 1 - max(a, b),
         "imp": lambda a, b: max(1 - a, b), "xor": lambda a, b: max(min(a, 1 - b), min(1 - a, b)),
         "xnor": lambda a, b: 1 - max(min(a, 1 - b), min(1 - a, b))}


def sec3_fractional(a=Fr(3, 10), b=Fr(7, 10)):
    print("-" * 72)
    print(f"3. THE CURATOR'S A = {a}, B = {b}: FRECHET INTERVALS AGAINST FUZZY MIN/MAX")
    want = {"and": (0, Fr(3, 10)), "or": (Fr(7, 10), 1), "nand": (Fr(7, 10), 1), "nor": (0, Fr(3, 10)),
            "imp": (Fr(7, 10), 1), "xor": (Fr(2, 5), 1), "xnor": (0, Fr(3, 5))}
    for name, bits in CONN.items():
        iv = interval_out(table(bits), (a, a), (b, b))
        fz = FUZZY[name](a, b)
        assert iv == tuple(Fr(x) for x in want[name]), (name, iv)
        at_end = fz in iv
        assert at_end == (name not in ("xor", "xnor")), (name, fz, iv)
        assert iv[0] <= fz <= iv[1]
        p11 = a * b
        point = p11 * bits[3] + (a - p11) * bits[2] + (b - p11) * bits[1] + (1 - a - b + p11) * bits[0]
        assert iv[0] <= point <= iv[1]                     # independence, stipulated, lands inside
        print(f"   {name:5s} fuzzy {float(fz):.2f}  interval [{float(iv[0]):.2f}, {float(iv[1]):.2f}]"
              f"  independent {float(point):.2f}" + ("   fuzzy = an end" if at_end else "   fuzzy inside"))


def sec4_clean_and_dirty(a=Fr(3, 10)):
    print("-" * 72)
    print(f"4. ONE ATOM OF DEGREE {a}: ONE FACT (CLEAN) AGAINST A READ PER OCCURRENCE (DIRTY)")
    # clean: A and not-A are one event and its complement — exact
    clean_and, clean_or = (ZERO, ZERO), (ONE, ONE)
    # dirty: two reads, two events of degree a and 1 - a, joint free
    dirty_and = interval_out(table(CONN["and"]), (a, a), (1 - a, 1 - a))
    dirty_or = interval_out(table(CONN["or"]), (a, a), (1 - a, 1 - a))
    assert dirty_and == (ZERO, min(a, 1 - a)) and dirty_or == (max(a, 1 - a), ONE)
    print(f"   A and not-A: clean [0, 0]; dirty [{float(dirty_and[0])}, {float(dirty_and[1])}]")
    print(f"   A or not-A:  clean [1, 1]; dirty [{float(dirty_or[0])}, {float(dirty_or[1])}]")
    print("   the dirty rule decides, not the numbers: one fact obeys the classical laws, two reads may not")


def sec5_sabotage():
    print("-" * 72)
    print("5. TWO SABOTAGES THE CHECKS MUST CATCH")
    global project, degree_01
    real_p, real_d = project, degree_01
    caught = 0
    project = lambda iv: T if iv[1] > 0 else F                # 'T if it may be true' — truth on credit
    try:
        sec1_sixteen()
    except AssertionError:
        caught += 1
    finally:
        project = real_p
    degree_01 = lambda phi, marking, separate: real_d(phi, marking, False)   # dirty reads made one event
    try:
        sec2_formulas(n=60)
    except AssertionError:
        caught += 1
    finally:
        degree_01 = real_d
    assert caught == 2, caught
    print("   truth on credit (T if hi > 0): caught by section 1; dirty reads merged into one event: caught by")
    print("   section 2 — the agreement above is not vacuous")


if __name__ == "__main__":
    sec1_sixteen()
    sec2_formulas()
    sec3_fractional()
    sec4_clean_and_dirty()
    sec5_sabotage()
    print("-" * 72)
    print("ZFRECHET: interval logic sits on ZTL with no verdict moved.")
