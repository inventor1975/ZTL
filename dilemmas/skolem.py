# -*- coding: utf-8 -*-
"""
Skolem's paradox, judged: "countable" names no universe of functions, and the paradox is two readings of one word.

Löwenheim–Skolem (Skolem 1922): a first-order theory with an infinite model has a countable model. So ZFC, if it has a
model at all, has a countable one, M. Yet ZFC proves "there is an uncountable set" (the reals), and M satisfies it.
A countable model in which the reals are uncountable: the paradox.

THE FORMALISATION, IN WORDS FIRST — a bad skeleton refutes a straw man:
  "S is countable" means "SOME function from the naturals onto S exists" — and "exists" ranges over a universe of
  functions that the sentence does not name. Two readings of "the reals of M are countable":
    INSIDE M    the functions are those M contains. M satisfies ZFC, so M contains no enumeration of its reals:
                REFUTED there (Cantor's diagonal argument runs inside M, against every enumeration M has).
    OUTSIDE     the functions are all functions. M is countable, so its reals are a countable set: EARNED — but only
                given that a model of ZFC exists at all, i.e. Con(ZFC), which ZFC cannot prove (Gödel). Unstipulated:
                OPEN, cure "stipulate Con(ZFC)"; stipulated: EARNED on a declared ground.
  With the universe unnamed the sentence is OPEN, its cure "name the universe of functions". There is no contradiction:
  the outside enumeration of M's reals is not an element of M, and its diagonal is a real that M does not have.

MEASURED HERE, on finite stand-ins (each section asserts what it prints):
  1. "X and Y are equinumerous" relative to a STOCK of functions: for X, Y of two elements, all 16 stocks of the 4
     functions X -> Y — the sentence is true in exactly the 12 stocks that contain a bijection, false in 4; the same
     two sets, opposite verdicts, by the stock alone;
  2. ILLUSTRATED, not measured (it holds by construction): Cantor's diagonal against an enumeration given from
     outside — the diagonal of any list of n strings of length n is not on the list. The finite stand-in cannot show
     the other half (a finite set is enumerable from inside too); that half is the theorem ZFC proves;
  3. the judge, its marks COMPUTED from section 1's stand-in: the stock unnamed OPEN ("name it"); a stock without a
     bijection (the inside reading) REFUTED; all functions (the outside reading) EARNED. And for ZFC itself: the
     outside reading rests on Con(ZFC) — unstipulated OPEN, stipulated EARNED.

NOT CLAIMED: anything new about Skolem's paradox (resolved by Skolem himself, 1922: "countable" is relative); which
universe is "the real one". Prior art: Skolem (1922); Benacerraf, "Skolem and the skeptic" (1985); Bays, "Reflections
on Skolem's paradox" (2000). What is added is the judge's form: a parameter left unnamed, and a premise (Con(ZFC)) on
which the outside reading rests.

Run:  python3 dilemmas/skolem.py
"""
import itertools
import os
import random
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from ztljudge import judge                                    # noqa: E402


def sec1():
    X, Y = (0, 1), ("a", "b")
    funcs = [dict(zip(X, ys)) for ys in itertools.product(Y, repeat=len(X))]
    is_bij = [len(set(f.values())) == len(Y) for f in funcs]
    true_in = false_in = 0
    for mask in range(1 << len(funcs)):
        stock = [i for i in range(len(funcs)) if mask >> i & 1]
        if any(is_bij[i] for i in stock):
            true_in += 1
        else:
            false_in += 1
    assert (true_in, false_in) == (12, 4) and sum(is_bij) == 2
    inside_stock = [i for i in range(len(funcs)) if not is_bij[i]]          # every function but the bijections
    marks = {"inside": "T" if any(is_bij[i] for i in inside_stock) else "F",
             "outside": "T" if any(is_bij) else "F"}
    print(f"   X = {{0, 1}}, Y = {{a, b}}: {len(funcs)} functions, {sum(is_bij)} of them bijections; over all "
          f"{1 << len(funcs)} stocks,")
    print(f"   'X and Y are equinumerous' is true in {true_in} (a bijection in stock) and false in {false_in} — "
          "the same sets, by the stock alone")
    return marks


def sec2(trials=300, n=8):
    rng = random.Random(1922)
    for _ in range(trials):
        R_M = set()
        while len(R_M) < n:
            R_M.add(tuple(rng.randint(0, 1) for _ in range(n)))
        e = list(R_M)
        rng.shuffle(e)                                           # an enumeration from OUTSIDE the model
        diag = tuple(1 - e[i][i] for i in range(n))
        assert diag not in R_M                                   # by construction: differs from the i-th at place i
    print(f"   illustrated on {trials} seeded lists of {n} strings of length {n}: the diagonal is never on the list —")
    print("   by construction, as Cantor's argument says. The other half (no enumeration INSIDE a model of ZFC) is the")
    print("   theorem ZFC proves; a finite stand-in cannot show it, since a finite set is enumerable from inside too")


def sec3(marks):
    unnamed = judge("equinumerous", {"equinumerous": "Z"})
    inside = judge("equinumerous", {"equinumerous": marks["inside"]})
    outside_small = judge("equinumerous", {"equinumerous": marks["outside"]})
    outside_open = judge("con_zfc & (con_zfc -> M_countable)", {"con_zfc": "Z", "M_countable": "T"})
    outside = judge("con_zfc & (con_zfc -> M_countable)", {"con_zfc": "T", "M_countable": "T"})
    assert unnamed["disposition"] == "OPEN" and inside["disposition"] == "REFUTED"
    assert outside_small["disposition"] == "EARNED"
    assert outside_open["disposition"] == "OPEN" and outside["disposition"] == "EARNED"
    print(f"   the stand-in, marks computed in section 1: the stock unnamed {unnamed['disposition']} (cure: name it);")
    print(f"   the stock without a bijection (inside) {inside['disposition']}; all functions (outside) "
          f"{outside_small['disposition']}")
    print("   ZFC itself: inside M, ZFC's theorem 'the reals are uncountable' holds in M: 'countable in M' REFUTED")
    print(f"   outside (all functions), Con(ZFC) unstipulated: {outside_open['disposition']} (cure: stipulate it);"
          f" stipulated: {outside['disposition']}")


if __name__ == "__main__":
    print("-" * 72)
    print("1. EQUINUMEROUS RELATIVE TO A STOCK OF FUNCTIONS")
    marks = sec1()
    print("-" * 72)
    print("2. THE DIAGONAL FROM OUTSIDE (an illustration)")
    sec2()
    print("-" * 72)
    print("3. THE JUDGE")
    sec3(marks)
    print("-" * 72)
    print("SKOLEM: all measurements hold — 'countable' was two words; inside REFUTED, outside EARNED on Con(ZFC).")
