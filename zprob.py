# -*- coding: utf-8 -*-
"""
Expedition E9: the probabilistic bridge. Why Z is not p=0.5.

Three measurements:
  1. REPARAMETRIZATION (Bertrand): a uniform prior made from ignorance
     gives different answers in different parametrizations of the same
     ignorance; Z does not.
  2. DEMPSTER–SHAFER: ZTL verdicts = the threshold case of Bel/Pl
     (T ⟺ Bel=1 "forced by all", F ⟺ Pl=0 "excluded by all", else Z);
     the interval cardinality of E5 = [Bel-count, Pl-count].
  3. ELLSBERG: the "irrational" preference of known risk over unknown
     uncertainty is zero-trust rationality.

Twin #5: imprecise probabilities (Walley 1991, lower/upper previsions)
— the lazy register of probabilities.
"""

from fractions import Fraction

from ztl import T, F, Z

# ------------------------------------------------------- 1. Bertrand
def bertrand():
    print("### 1. Reparametrization: a prior launders ignorance, Z does not")
    print("  Given: about w we know ONLY w ∈ [0,1]. Question: \"w ≤ 0.25?\"")
    p_w = Fraction(1, 4)              # uniform prior on w
    # the same ignoramus, but thinking in the parameter y = w² (also ∈ [0,1]):
    p_y = Fraction(1, 16)             # P(w ≤ 1/4) = P(y ≤ 1/16)
    print(f"  Bayesian in parameter w  (uniform on w):  P = {p_w}")
    print(f"  Bayesian in parameter w² (uniform on w²): P = {p_y}")
    print("  One ignorance — TWO different numbers: the prior imported")
    print("  information that was not there (parametrization choice = hidden knowledge).")
    verdict = Z                        # the atom "w ≤ 0.25" at w∈[0,1]: not forced
    print(f"  ZTL atom \"w ≤ 0.25\" at w∈[0,1]: {verdict} — both in parameter w")
    print("  and in parameter w² (the interval [0,1] ↔ [0,1]): invariant.")
    print("  Ignorance does not convert into a number without importing information.\n")


# ------------------------------------------------- 2. Dempster–Shafer
def ds_bel_pl(masses, event, frame):
    bel = sum(m for s, m in masses.items() if set(s) <= set(event))
    pl = sum(m for s, m in masses.items() if set(s) & set(event))
    return bel, pl


def dempster_shafer():
    print("### 2. Dempster–Shafer: ZTL verdicts = Bel/Pl thresholds")
    frame = "abc"
    masses = {"a": Fraction(1, 2), "abc": Fraction(1, 2)}  # half-knowledge
    print("  Masses: m({a})=1/2, m({a,b,c})=1/2 (partial ignorance)")
    for event in ("abc", "a", "b", "bc", ""):
        bel, pl = ds_bel_pl(masses, event, frame)
        if bel == 1:
            v = T
        elif pl == 0:
            v = F
        else:
            v = Z
        shown = "{" + ",".join(event) + "}"
        print(f"  event {shown:8s} Bel={str(bel):4s} Pl={str(pl):4s}"
              f"  ZTL verdict: {v}")
    print("  T ⟺ Bel=1 (forced by all readings of the ignorance),")
    print("  F ⟺ Pl=0 (excluded by all), else Z. The generating principle")
    print("  is the {0,1}-threshold of Dempster–Shafer theory; the interval")
    print("  cardinality of E5 = [Bel-count, Pl-count] elementwise.\n")


# ------------------------------------------------------ 3. Ellsberg
def ellsberg():
    print("### 3. Ellsberg: the zero-trust rationality of \"irrationality\"")
    print("  Urn K: 50 red / 50 black (VERIFIED). Urn U: 100 balls,")
    print("  composition unknown (mark p_red ∈ [0,1]). Bet on red: +100.")
    ev_K = (Fraction(1, 2) * 100, Fraction(1, 2) * 100)   # [50,50]
    ev_U = (Fraction(0), Fraction(100))                     # [0,100]
    print(f"  EV(K) ∈ [{ev_K[0]},{ev_K[1]}] — an earned number")
    print(f"  EV(U) ∈ [{ev_U[0]},{ev_U[1]}] — an interval of ignorance")
    atom = Z if not (ev_U[0] >= ev_K[1] or ev_U[1] < ev_K[0]) else T
    print(f"  Atom \"U is no worse than K\": {atom} — not forced ⇒ default deny ⇒")
    print("  choose K. The subjects of Ellsberg's experiment (1961) choose K and")
    print("  are declared \"irrational\" relative to the Bayesian norm —")
    print("  but they simply distinguish risk (a verified p) from ignorance")
    print("  (a mark), which a point prior cannot distinguish.\n")


if __name__ == "__main__":
    print("=" * 72)
    print("E9. THE PROBABILISTIC BRIDGE: Z ≠ p=0.5")
    print("=" * 72 + "\n")
    bertrand()
    dempster_shafer()
    ellsberg()
    print("### Summary: the second \"SQL theorem\" — about Bayesians")
    print("  A point prior from ignorance = greedy laundering of Z into a")
    print("  number: the same substitution as SQL's DISTINCT (equality of")
    print("  marks instead of equality of values), and it is punishable")
    print("  (reparametrization gives contradicting answers). The honest")
    print("  architecture is two-registered: ignorance lives in mass intervals")
    print("  (the lazy register: Dempster–Shafer, Walley's imprecise")
    print("  probabilities — TWIN #5), decisions are made by forcedness")
    print("  verdicts (the greedy register). Bayes stays honest on VERIFIED")
    print("  probabilities — that is his C-extension; only minting numbers")
    print("  out of emptiness is forbidden.")
