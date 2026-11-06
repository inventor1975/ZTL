# -*- coding: utf-8 -*-
"""
Diophantine equations, judged: "it has a root" and "it has no root" are earned on different grounds.

Asked 2026-11-05/06 by the curator, after Terence Tao's remark in an interview (Lex Fridman) that whether some
polynomial equations have solutions depends on the axioms: "у нас же всё без аксиом — стоит исследовать". The known
fact (Matiyasevich–Robinson–Davis–Putnam, 1970): for any consistent effective theory T there is a polynomial P_T with
integer coefficients such that "P_T = 0 has no root in the naturals" is equivalent to "T is consistent" — so T does not
decide it (Gödel). The catch handed over at once: our "no axioms" is the empty `#print axioms` list in Lean, not the
absence of a theory; Lean's own theory has its own such polynomial.

THE FORMALISATION, IN WORDS FIRST — three kinds of claim about a polynomial P:
    HAS A ROOT       earned by ONE finite witness, checked by substitution;
    NO ROOT UP TO B  earned by a search;
    NO ROOT          never earned by a search, however far — earned only by a PROOF in a named theory, and then
                     relative to that theory; refuted by one witness.
  So the two directions are not symmetric: a root is shown, an absence is proved.

MEASURED HERE (each section asserts what it prints):
  1. Pell's equation x² − 61y² = 1: a search over every y ≤ 10⁶ finds no root; the continued fraction of √61 gives the
     smallest root, x = 1 766 319 049, y = 226 153 980 — checked by substitution, and in Lean (`ZDiophantine.
     pell61_witness`, zero axioms). The inference "searched far, so no root" is false here;
  2. x² = 3y + 2: a search to 10⁶ finds no root, and that earns nothing; the proof does (squares are 0 or 1 modulo 3:
     `ZDiophantine.no_root_three`, zero axioms) — checked here on every x < 10⁶ for the residues it uses;
  3. the judge, marks from sections 1–2: Pell "has a root" OPEN before the witness, EARNED after; "no root" from the
     search alone OPEN, refuted by the witness (a naive "searched, so no root" would have been EARNED and wrong);
     x² = 3y + 2 "no root" EARNED on the proof, OPEN on the search alone;
  4. the polynomial of a theory's consistency (cited facts, not computed: MRDP and Gödel): "P_ZFC has no root" on the
     ground ZFC — OPEN for good if ZFC is consistent; on the ground ZFC + an inaccessible cardinal — EARNED (that
     theory proves Con(ZFC)); a root, if one were ever found — REFUTED, and ZFC inconsistent. Lean's theory is believed
     to sit above ZFC (Carneiro 2019: with its three axioms it is equiconsistent with ZFC plus n inaccessibles for every
     n; the axiom-free fragment is less studied), so it would decide P_ZFC — and has its own P_Lean it cannot.

NOT CLAIMED: anything new about MRDP or incompleteness. What is added is the judge's form: the ground of a "no" is
named, and a search is never mistaken for one.

Run:  python3 dilemmas/diophantine.py
"""
import os
import sys
from math import isqrt

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from ztljudge import judge                                    # noqa: E402

BOUND = 10 ** 6


def pell_fundamental(D):
    """the smallest x, y >= 1 with x² − D y² = 1, by the continued fraction of √D (exact integers)"""
    a0 = isqrt(D)
    m, d, a = 0, 1, a0
    h_prev, h = 1, a0
    k_prev, k = 0, 1
    while h * h - D * k * k != 1:
        m = d * a - m
        d = (D - m * m) // d
        a = (a0 + m) // d
        h_prev, h = h, a * h + h_prev
        k_prev, k = k, a * k + k_prev
    return h, k


def sec1():
    found = [y for y in range(1, BOUND + 1) if isqrt(61 * y * y + 1) ** 2 == 61 * y * y + 1]
    assert found == []
    x, y = pell_fundamental(61)
    assert (x, y) == (1766319049, 226153980) and x * x - 61 * y * y == 1 and y > BOUND
    # both sides: the same search finds D = 2's root at once (3² − 2·2² = 1)
    assert [y for y in range(1, 10) if isqrt(2 * y * y + 1) ** 2 == 2 * y * y + 1][0] == 2
    print(f"   x² − 61y² = 1: no root with y <= {BOUND:,} (searched); the smallest root is x = {x:,}, y = {y:,}")
    print("   (continued fraction of √61), checked by substitution and in Lean (ZDiophantine.pell61_witness);")
    print("   control: the same search finds x² − 2y² = 1 at y = 2 at once")
    return {"searched_no_root": True, "witness": True}


def sec2():
    found = [x for x in range(BOUND) if x * x >= 2 and (x * x - 2) % 3 == 0]
    assert found == []
    residues = {x * x % 3 for x in range(BOUND)}
    assert residues == {0, 1}
    print(f"   x² = 3y + 2: no root with x < {BOUND:,} (searched — earns nothing for 'no root');")
    print("   the proof: every square is 0 or 1 modulo 3 (here: the residues of x² for x < 10⁶ are {0, 1}),")
    print("   proved for all x in Lean (ZDiophantine.no_root_three, zero axioms)")
    return {"proof": True}


def sec3(pell, three):
    has_before = judge("pell_has_root", {"pell_has_root": "Z"})
    has_after = judge("pell_has_root", {"pell_has_root": "T" if pell["witness"] else "Z"})
    none_search = judge("pell_no_root", {"pell_no_root": "Z"})                  # a search grounds no "no"
    none_after = judge("pell_no_root", {"pell_no_root": "F" if pell["witness"] else "Z"})
    naive = judge("pell_no_root", {"pell_no_root": "T" if pell["searched_no_root"] else "Z"})
    three_proof = judge("three_no_root", {"three_no_root": "T" if three["proof"] else "Z"})
    three_search = judge("three_no_root", {"three_no_root": "Z"})
    assert (has_before["disposition"], has_after["disposition"]) == ("OPEN", "EARNED")
    assert (none_search["disposition"], none_after["disposition"]) == ("OPEN", "REFUTED")
    assert naive["disposition"] == "EARNED"                                     # the false EARNED a naive rule makes
    assert (three_proof["disposition"], three_search["disposition"]) == ("EARNED", "OPEN")
    print(f"   Pell 'has a root': before the witness {has_before['disposition']}, after {has_after['disposition']}")
    print(f"   Pell 'no root': on the search alone {none_search['disposition']}, after the witness "
          f"{none_after['disposition']} (a naive 'searched, so no root' gives {naive['disposition']} — and is wrong)")
    print(f"   x² = 3y + 2 'no root': on the proof {three_proof['disposition']}, on the search alone "
          f"{three_search['disposition']}")


def sec4():
    on_zfc = judge("pzfc_no_root", {"pzfc_no_root": "Z"})            # cited: unprovable in ZFC if ZFC is consistent
    on_stronger = judge("pzfc_no_root", {"pzfc_no_root": "T"})       # cited: ZFC + an inaccessible proves Con(ZFC)
    on_root = judge("pzfc_no_root", {"pzfc_no_root": "F"})           # a root would be a finite witness against it
    assert (on_zfc["disposition"], on_stronger["disposition"], on_root["disposition"]) == ("OPEN", "EARNED", "REFUTED")
    print(f"   'P_ZFC has no root' (marks are cited facts, MRDP and Gödel): on the ground ZFC {on_zfc['disposition']}"
          " for good,")
    print(f"   if ZFC is consistent; on ZFC + an inaccessible {on_stronger['disposition']}; if a root were found "
          f"{on_root['disposition']} — and ZFC inconsistent")
    print("   Lean (Carneiro 2019) sits above ZFC: it would decide P_ZFC — and has its own P_Lean it cannot")


if __name__ == "__main__":
    print("-" * 72)
    print("1. A ROOT IS SHOWN: PELL 61")
    pell = sec1()
    print("-" * 72)
    print("2. AN ABSENCE IS PROVED: x² = 3y + 2")
    three = sec2()
    print("-" * 72)
    print("3. THE JUDGE")
    sec3(pell, three)
    print("-" * 72)
    print("4. A THEORY'S OWN POLYNOMIAL")
    sec4()
    print("-" * 72)
    print("DIOPHANTINE: all measurements hold — a root is shown, an absence is proved, and the ground of a 'no' is named.")
