# -*- coding: utf-8 -*-
"""
What a theorem COSTS here: proving in ZTL, measured on a real one.

The curator's question: is proving hard in this logic? The question has
to be re-aimed first, because "hard" measures the wrong thing. Length of
derivation is not our currency — from an empty ledger nothing is
derivable at all (E26). The currency is the VERIFICATION BILL: how many
atoms must be witnessed before the theorem is earned.

Measured on the pigeonhole principle (3 pigeons, 2 holes — a real
theorem, classically a tautology):

  * it is a ZTL tautology too — 729 markings out of 729 — but read that
    number carefully: with nothing verified the ANTECEDENT is F, so the
    theorem holds VACUOUSLY. Default deny makes conditionals cheap, and
    this is a trap in our own instrument, recorded here as one;
  * non-vacuously it also holds: of the 729 markings, 125 earn the
    antecedent, and in every one of them the conclusion is T;
  * the bill is exactly 3 atoms — one per pigeon, the minimum that could
    possibly say where the pigeons are. The theorem is charged the price
    of its own subject matter, and not a coin more.

And the correction this stand forced on its own author: proof by cases
is NOT lost. `((p→q) ∧ (¬p→q)) → q` is ZTL-valid. What is lost is
asserting `p ∨ ¬p` about an unchecked p — and the case schema, though
valid, never fires unless q is already decided, because a BARE ATOM is
never earned by inference. A COMPOUND claim is: the pigeonhole conclusion
is earned from three verified atoms while three others stay marks. That
is the exact shape of "rules transport, they do not mint".

Run:  python3 zprove.py
"""
import os
import sys
from itertools import combinations, product

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from ztl import T, F, Z, ev                                  # noqa: E402

V = (T, F, Z)
ATOMS = [f"p{i}{j}" for i in range(3) for j in range(2)]


def _or(*xs):
    r = xs[0]
    for x in xs[1:]:
        r = ("or", r, x)
    return r


def _and(*xs):
    r = xs[0]
    for x in xs[1:]:
        r = ("and", r, x)
    return r


HOUSED = _and(*[_or(f"p{i}0", f"p{i}1") for i in range(3)])
SHARE = _or(*[_and(f"p{i}{j}", f"p{k}{j}")
              for i, k in combinations(range(3), 2) for j in range(2)])
PIGEONHOLE = ("imp", HOUSED, SHARE)


def sec1_classically():
    print("-" * 72)
    print("1. THE THEOREM, CLASSICALLY")
    cl = [dict(zip(ATOMS, c)) for c in product((T, F), repeat=6)]
    assert all(ev(PIGEONHOLE, m) == T for m in cl)
    print("   3 pigeons, 2 holes: if every pigeon is housed, two share a")
    print(f"   hole. A tautology on all {len(cl)} classical assignments.")


def sec2_the_vacuity_trap():
    print("-" * 72)
    print("2. IN ZTL — AND THE TRAP IN THE NUMBER")
    allm = [dict(zip(ATOMS, c)) for c in product(V, repeat=6)]
    vals = [ev(PIGEONHOLE, m) for m in allm]
    nothing = {a: Z for a in ATOMS}
    print(f"   valid on all {len(allm)} markings: {all(v == T for v in vals)}")
    print(f"   but with NOTHING verified: antecedent = "
          f"{ev(HOUSED, nothing)}, theorem = {ev(PIGEONHOLE, nothing)}")
    assert all(v == T for v in vals)
    assert ev(HOUSED, nothing) == F and ev(PIGEONHOLE, nothing) == T
    print("   — an empty truth. Under default deny an unverified antecedent")
    print("   is FALSE, so every conditional over unchecked atoms is valid")
    print("   for free. This is a trap in our own instrument: 'ZTL-valid'")
    print("   for a conditional must always be read together with 'and its")
    print("   antecedent is earnable at all'.")
    return allm


def sec3_the_bill(allm):
    print("-" * 72)
    print("3. NON-VACUOUSLY, AND THE BILL")
    live = [m for m in allm if ev(HOUSED, m) == T]
    holds = all(ev(SHARE, m) == T for m in live)
    bill = min(sum(1 for v in m.values() if v != Z) for m in live)
    cheapest = [m for m in live
                if sum(1 for v in m.values() if v != Z) == bill][0]
    print(f"   markings that EARN the antecedent: {len(live)} of {len(allm)}")
    print(f"   in every one of them the conclusion is T: {holds}")
    print(f"   minimum verification bill: {bill} atoms — e.g. "
          f"{sorted(k for k, v in cheapest.items() if v != Z)}")
    assert holds and bill == 3 and len(live) == 125
    print("   one witness per pigeon: exactly the data the theorem is")
    print("   about, and not one coin more. That is what a proof costs")
    print("   here — not steps, but witnesses.")
    return live


def sec4_the_correction():
    print("-" * 72)
    print("4. THE CORRECTION: case analysis is NOT lost")
    schemas = {
        "case analysis ((p→q)∧(¬p→q))→q":
            ("imp", ("and", ("imp", "p", "q"),
                     ("imp", ("not", "p"), "q")), "q"),
        "Peirce        ((p→q)→p)→p":
            ("imp", ("imp", ("imp", "p", "q"), "p"), "p"),
        "reductio      (p→F)→¬p":
            ("imp", ("imp", "p", F), ("not", "p")),
        "syllogism     (p→q)∧(q→r)→(p→r)":
            ("imp", ("and", ("imp", "p", "q"), ("imp", "q", "r")),
             ("imp", "p", "r")),
        "modus ponens  (p→q)∧p→q":
            ("imp", ("and", ("imp", "p", "q"), "p"), "q"),
        "excluded middle p∨¬p":
            ("or", "p", ("not", "p")),
    }
    results = {}
    for name, phi in schemas.items():
        names = sorted({a for a in ("p", "q", "r") if a in str(phi)})
        ms = [dict(zip(names, c)) for c in product(V, repeat=len(names))]
        valid = all(ev(phi, m) == T for m in ms)
        results[name] = valid
        print(f"   {name:34} ZTL-valid: {valid}")
    assert results["case analysis ((p→q)∧(¬p→q))→q"] is True
    assert results["reductio      (p→F)→¬p"] is True
    assert results["syllogism     (p→q)∧(q→r)→(p→r)"] is True
    assert results["modus ponens  (p→q)∧p→q"] is True
    assert results["Peirce        ((p→q)→p)→p"] is False
    assert results["excluded middle p∨¬p"] is False
    print("   so the working kit survives: modus ponens, syllogism,")
    print("   reductio, even proof by cases. Peirce's law — the one that")
    print("   separates classical from intuitionistic logic — does not,")
    print("   and neither does excluded middle on an unchecked atom.")
    print("   Earlier in this session the author said 'we cannot do case")
    print("   analysis'; the machine says otherwise, and the machine is")
    print("   right. The correct statement is the next section.")


def sec5_transport_not_mint(live):
    print("-" * 72)
    print("5. WHAT INFERENCE CAN AND CANNOT DO")
    # a BARE ATOM is never earned by inference: for the case schema, every
    # marking that fires it has q already decided
    phi = ("imp", ("and", ("imp", "p", "q"),
                   ("imp", ("not", "p"), "q")), "q")
    ms = [dict(zip(("p", "q"), c)) for c in product(V, repeat=2)]
    fires = [m for m in ms if ev(phi[1], m) == T]
    print(f"   case analysis fires on {len(fires)} markings, and in every")
    print(f"   one of them q is already verified: "
          f"{all(m['q'] != Z for m in fires)}")
    assert fires and all(m["q"] != Z for m in fires)
    # a COMPOUND claim is earned from verified atoms while others stay marks
    cheap = [m for m in live
             if sum(1 for v in m.values() if v != Z) == 3][0]
    marks = [k for k, v in cheap.items() if v == Z]
    print(f"   yet the pigeonhole conclusion IS earned with {len(marks)} of")
    print(f"   6 atoms still unverified ({sorted(marks)}): "
          f"{ev(SHARE, cheap)}")
    assert ev(SHARE, cheap) == T and len(marks) == 3
    print("   so inference is a TRANSPORTER: it carries verification from")
    print("   atoms into compound claims — that is real work, and the")
    print("   pigeonhole is real proof — but it never mints the first coin.")
    print("   A bare atom enters only by being witnessed. Which is the")
    print("   whole doctrine, stated as a measurement rather than a motto.")


if __name__ == "__main__":
    print("=" * 72)
    print("PROVING IN ZTL — the pigeonhole, and what it costs")
    print("=" * 72)
    sec1_classically()
    allm = sec2_the_vacuity_trap()
    live = sec3_the_bill(allm)
    sec4_the_correction()
    sec5_transport_not_mint(live)
    print("=" * 72)
    print("ZPROVE GREEN — a real theorem goes through: valid, and valid")
    print("non-vacuously on 125 markings, for a bill of exactly 3 witnessed")
    print("atoms — the price of its own subject matter. The working kit")
    print("(MP, syllogism, reductio, proof by cases) survives; Peirce and")
    print("excluded middle on an unchecked atom do not. Inference")
    print("transports verification into compound claims and never mints")
    print("the first coin. And conditionals over unverified antecedents are")
    print("valid for free — a trap of our own making, now under assert.")
