# -*- coding: utf-8 -*-
"""hardy — Hardy's paradox (1992/93) through the ZTL lens, with a MECHANICAL grounding rule.

The curator's plan of 2026-10-04: first a grounding rule that leaves the encoder no freedom, then problems.
The prediction was written BEFORE this file ran (ztl-private/notes/HARDY-PREDICTION-2026-10-04.md, ~21:10).

  THE SETUP. |psi> = (|00> + |01> + |10>)/sqrt3. Alice and Bob each ask one question, Z (0/1) or X (+/-).
  From amplitudes: P(X_A=-, X_B=-) = 1/12; P(X_A=-, Z_B=0) = 0; P(Z_A=0, X_B=-) = 0; P(Z_A=1, Z_B=1) = 0.
  The chain in a run with X_A = X_B = -: "had Bob asked Z he would get 1", "had Alice asked Z she would get
  1", so both 1 — which never happens. Bell's theorem without inequalities.

  THE GROUNDING RULE (one rule, written before any case used it). In a run each party asked ONE question:
    - an atom about the question ASKED: T if it names the answer obtained, F otherwise (witnessed);
    - an atom about a question NOT asked whose projector does not COMMUTE with the asked one: Z, and it is
      not in the repertoire (the asked question cannot be un-asked) -> Z_PERMANENT;
    - an atom whose projector commutes with the asked one would be fixed by it (does not occur here).
  Commutation is COMPUTED from the projectors; the encoder chooses nothing.

  H1  THE PHYSICS, from amplitudes (asserted).
  H2  THE CONTESTED RUN (X_A = X_B = -), grounded by the rule: the chain is REFUTED for every value of the
      two unasked answers (both Z_PERMANENT, ceiling frozen); each law alone is not refuted (OPEN / ON
      CREDIT); the observed answers stay EARNED. What falls is "the unasked questions have answers".
  H3  THE CONTROL, where the rule could fail: in a run where Bob DID ask Z after Alice got X = -, the rule
      must earn "Z_B = 1" and the link "X_A=- -> Z_B=1" (and the mirror run, and the Z-Z law).
  H4  THE WHOLE RUN SPACE: every pair of questions, every outcome with P > 0 — the rule never makes any of
      the three probability-1 laws come out REFUTED (a rule that put a witnessed value where physics forbids
      it would). Measured: 13 runs x 3 laws, refuted 0, earned 17.

  PRIOR ART, plainly: Hardy, PRL 68, 2981 (1992) and PRL 71, 1665 (1993); Mermin, "Quantum mysteries refined"
  (Am. J. Phys. 1994). The standard reading: counterfactual definiteness or locality fails. The lens takes the
  first, for the operational reason shared with bell.py B3 (unmade readings). What is new here is the
  mechanical grounding rule and its control, not the resolution.

Run:  python3 dilemmas/hardy.py        (asserts every measurement)
"""

import itertools
import math
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

from ztljudge import judge          # noqa: E402
from zredeem import ceiling, stamp  # noqa: E402

S3, R2 = 1 / math.sqrt(3), 1 / math.sqrt(2)
PSI = {(0, 0): S3, (0, 1): S3, (1, 0): S3, (1, 1): 0.0}
BASIS = {"Z": {"0": (1.0, 0.0), "1": (0.0, 1.0)}, "X": {"+": (R2, R2), "-": (R2, -R2)}}
# the atoms of the chain: (party, question, answer)
ATOMS = {"xa_m": ("A", "X", "-"), "xb_m": ("B", "X", "-"), "za_1": ("A", "Z", "1"), "zb_1": ("B", "Z", "1")}
CHAIN = "xa_m & xb_m & (xa_m -> zb_1) & (xb_m -> za_1) & ~(za_1 & zb_1)"
LAWS = ("xa_m -> zb_1", "xb_m -> za_1", "~(za_1 & zb_1)")   # the three certainties (probability 1)


def prob(qa, oa, qb, ob):
    va, vb = BASIS[qa][oa], BASIS[qb][ob]
    amp = sum(PSI[(i, j)] * va[i] * vb[j] for i in (0, 1) for j in (0, 1))
    return amp * amp


def commutator(u, v):
    P = [[u[a] * u[b] for b in range(2)] for a in range(2)]
    Q = [[v[a] * v[b] for b in range(2)] for a in range(2)]
    PQ = [[sum(P[i][k] * Q[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
    QP = [[sum(Q[i][k] * P[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
    return max(abs(PQ[i][j] - QP[i][j]) for i in range(2) for j in range(2))


def ground(run):
    """THE RULE. run = {"A": (question, answer), "B": (question, answer)} -> (marking, repertoire)."""
    m, rep = {}, set()
    for name, (party, q, ans) in ATOMS.items():
        asked_q, asked_ans = run[party]
        if q == asked_q:
            m[name] = "T" if ans == asked_ans else "F"
            rep.add(name)
        elif commutator(BASIS[q][ans], BASIS[asked_q][asked_ans]) > 1e-9:
            m[name] = "Z"                          # unasked and incompatible: no act can witness it now
        else:
            raise AssertionError(f"{name}: commutes with the asked question — the rule has no case for it")
    return m, rep


def run():
    print("HARDY'S PARADOX — through the ZTL lens, grounded by one mechanical rule")
    print("=" * 72)

    print("\n### H1. The physics, from amplitudes")
    p_mm, p_m0, p_0m, p_11 = prob("X", "-", "X", "-"), prob("X", "-", "Z", "0"), prob("Z", "0", "X", "-"), prob("Z", "1", "Z", "1")
    print(f"ok  P(X_A=-, X_B=-) = {p_mm:.4f} (1/12);  P(X_A=-, Z_B=0) = {p_m0:.4f};  P(Z_A=0, X_B=-) = {p_0m:.4f};"
          f"  P(Z_A=1, Z_B=1) = {p_11:.4f}")
    assert abs(p_mm - 1 / 12) < 1e-12 and max(p_m0, p_0m, p_11) < 1e-12
    cz = commutator(BASIS["Z"]["1"], BASIS["X"]["-"])
    print(f"ok  [Z=1, X=-] = {cz:.3f}: the two questions cannot be asked together")
    assert cz > 0.1

    print("\n### H2. The contested run: both asked X, both got -")
    m, rep = ground({"A": ("X", "-"), "B": ("X", "-")})
    r = judge(CHAIN, m)
    c = ceiling(CHAIN, m, rep)
    st = {a: stamp(a, m, rep) for a in ATOMS}
    print(f"ok  grounding by the rule: {m}")
    print(f"ok  chain: {r['disposition']}, weak links {sorted(r['unverified'])}, ceiling frozen = {c['ceiling_frozen']}")
    print(f"ok  stamps: {st}")
    assert m == {"xa_m": "T", "xb_m": "T", "za_1": "Z", "zb_1": "Z"}
    assert r["disposition"] == "REFUTED" and sorted(r["unverified"]) == ["za_1", "zb_1"] and c["ceiling_frozen"]
    assert st["za_1"] == st["zb_1"] == "Z_PERMANENT" and st["xa_m"] == st["xb_m"] == "GROUNDED"
    for a in ("xa_m", "xb_m"):
        assert judge(a, m)["disposition"] == "EARNED"
    laws = {law: judge(law, m)["disposition"] for law in LAWS}
    print(f"ok  each law ALONE in this run: {laws} — none refuted")
    assert "REFUTED" not in laws.values()
    print("ok  READING: the witnessed atoms are all T, each law alone survives; only their conjunction is false, and")
    print("    false for EVERY value of the two unasked answers ('false regardless'): what is refuted is that the")
    print("    unasked questions HAVE answers at all. (judge's 'unverified' lists every Z atom present; here they are")
    print("    exactly the two unasked answers.)")

    print("\n### H3. The control: where the rule could have failed")
    assert prob("X", "-", "Z", "0") < 1e-12 < prob("X", "-", "Z", "1")     # given X_A=-, Bob's Z is surely 1
    m, rep = ground({"A": ("X", "-"), "B": ("Z", "1")})
    d1, d2 = judge("zb_1", m)["disposition"], judge("xa_m -> zb_1", m)["disposition"]
    print(f"ok  Alice X=-, Bob asked Z: 'Z_B=1' {d1}; link 'X_A=- -> Z_B=1' {d2}")
    assert d1 == "EARNED" and d2 == "EARNED"
    assert prob("Z", "0", "X", "-") < 1e-12 < prob("Z", "1", "X", "-")
    m, rep = ground({"A": ("Z", "1"), "B": ("X", "-")})
    d3, d4 = judge("za_1", m)["disposition"], judge("xb_m -> za_1", m)["disposition"]
    print(f"ok  mirror: 'Z_A=1' {d3}; link 'X_B=- -> Z_A=1' {d4}")
    assert d3 == "EARNED" and d4 == "EARNED"
    zz = []
    for oa, ob in itertools.product("01", repeat=2):
        if prob("Z", oa, "Z", ob) > 1e-12:
            m, _ = ground({"A": ("Z", oa), "B": ("Z", ob)})
            zz.append(judge("~(za_1 & zb_1)", m)["disposition"])
    print(f"ok  both asked Z, every possible run: '~(Z_A=1 & Z_B=1)' {sorted(set(zz))} ({len(zz)} runs)")
    assert set(zz) == {"EARNED"} and len(zz) == 3

    print("\n### H4. The whole run space: the rule never makes a law of physics come out refuted")
    # 04.10, first version of H4 was VACUOUS: it counted refutations with an empty 'unverified', but every run
    # has two Z atoms by construction, so it could never fail. This version CAN fail: a grounding rule that put
    # a witnessed value where physics forbids it would refute one of the probability-1 laws in some run.
    runs, refuted_laws, earned_laws = 0, [], 0
    for qa, qb in itertools.product("ZX", repeat=2):
        for oa, ob in itertools.product(BASIS[qa], BASIS[qb]):
            if prob(qa, oa, qb, ob) < 1e-12:
                continue
            runs += 1
            m, _ = ground({"A": (qa, oa), "B": (qb, ob)})
            for law in LAWS:
                d = judge(law, m)["disposition"]
                earned_laws += d == "EARNED"
                if d == "REFUTED":
                    refuted_laws.append((qa, oa, qb, ob, law))
    print(f"ok  {runs} possible runs x {len(LAWS)} laws: refuted {len(refuted_laws)}, earned {earned_laws}, the rest open")
    assert not refuted_laws and earned_laws > 0

    print("\nHARDY: all measurements hold.")
    print("The contradiction lands on two answers to questions nobody asked; every witnessed answer stays earned.")


if __name__ == "__main__":
    run()
