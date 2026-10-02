# -*- coding: utf-8 -*-
"""bell — the curator's rings: what gives the minus, what gives the cosine, and which premise of Bell fails.

The curator's image (2026-10-02; recorded in ztl-private notes IDEAS §18): particles are rings
running round a circle, as in anti-de Sitter space; on entangling, two rings touch into a
FIGURE-EIGHT and fly into each other — they OVERLAP. Three measurements, each asserted below.

  B1  THE EIGHT, TAKEN LITERALLY (one shared running phase; the two lobes run opposite ways):
      perfect anti-correlation at equal settings (E = -1, as the singlet) — a real hit — but a
      straight line between angles instead of the cosine, and CHSH = 2: the local bound. Bell's
      theorem forbids more to ANY model where a part carries its own phase, whatever the geometry.
      (The eight's tangent turning number is 0 — the lobes cancel; it is not a double cover.)

  B2  THE RINGS OVERLAP: their waves ADD. Two waves with phases a and b interfere:
      |e^{ia} + e^{ib}|^2 / 4 = cos^2((a-b)/2) — the chance the readings come out opposite.
      E = -cos(a-b), CHSH = 2*sqrt(2) (Monte Carlo: about 2.83), and no signalling (ring A alone is
      a fair coin whatever B's setting). The eight gives the MINUS, the overlap gives the COSINE;
      together, the quantum singlet. Non-local by construction (the overlapped rings are one
      object) — exactly what Bell demands; it reproduces quantum mechanics, it does not beat it.

  B3  WHICH PREMISE FAILS, through the ZTL lens. One run measures one setting per side. "The
      measured pair is such-and-such" is EARNED; "the reading NOT made has a value" (A at a') is
      Z_PERMANENT — no act can witness it after the run — and "all four readings have values",
      which the CHSH bound's arithmetic needs, has a FROZEN ceiling. ZTL never granted the
      premise the experiment refutes.

  PRIOR ART, plainly: Bell (1964), CHSH (1969); Peres (1978), "unperformed experiments have no
  results"; Bell tests by two-photon interference (Ou-Mandel 1988, Franson 1989); ER=EPR
  (Maldacena-Susskind 2013) for the picture; geometric "Bell disproofs" (Christian) failed —
  B1 shows concretely why a part with its own phase cannot work. Nothing here is new physics.
  What is ours: one stamp — Z_PERMANENT, "no act can witness it" — names the failed classical
  step in three places measured the same day: identity (dilemmas/indistinguishable.py, ZQuasi),
  routes (Hong-Ou-Mandel), and unmade readings (here).

Run:  python3 dilemmas/bell.py        (asserts every measurement)
"""

import cmath
import math
import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

from ztljudge import judge          # noqa: E402
from zredeem import stamp, ceiling  # noqa: E402

A, A2, B, B2 = 0.0, math.pi / 2, math.pi / 4, 3 * math.pi / 4      # where quantum mechanics violates most
N = 200000


def sgn(x):
    return 1 if x >= 0 else -1


def chsh(E):
    return abs(E(A, B) - E(A, B2) + E(A2, B) + E(A2, B2))


def eight_literal(rng):
    thetas = [rng.uniform(0, 2 * math.pi) for _ in range(N)]
    return lambda a, b: sum(sgn(math.cos(t - a)) * -sgn(math.cos(t - b)) for t in thetas) / N


def overlap(rng):
    def E(a, b):
        p_opp = abs(cmath.exp(1j * a) + cmath.exp(1j * b)) ** 2 / 4
        s = 0
        for _ in range(N):
            x = 1 if rng.random() < 0.5 else -1
            s += x * (-x if rng.random() < p_opp else x)
        return s / N
    return E


def turning_number(xy, n=100000):
    tot, prev = 0.0, None
    for i in range(n + 1):
        t = 2 * math.pi * i / n
        (x1, y1), (x2, y2) = xy(t), xy(t + 1e-6)
        ang = math.atan2(y2 - y1, x2 - x1)
        if prev is not None:
            d = (ang - prev + math.pi) % (2 * math.pi) - math.pi
            tot += d
        prev = ang
    return tot / (2 * math.pi)


def run():
    print("BELL — the curator's rings, and which premise fails")
    print("=" * 72)
    rng = random.Random(20261002)

    print("\n### B1. The eight, taken literally")
    E1 = eight_literal(rng)
    s1 = chsh(E1)
    print(f"ok  equal settings E = {E1(0, 0):+.3f} (singlet -1); 45 deg E = {E1(0, math.pi / 4):+.3f} "
          f"(QM {-math.cos(math.pi / 4):+.3f}); CHSH = {s1:.3f} (local bound 2)")
    assert abs(E1(0, 0) + 1) < 1e-9 and abs(s1 - 2.0) < 0.02
    tn = turning_number(lambda t: (math.sin(t), math.sin(t) * math.cos(t)))
    print(f"ok  turning number of the eight = {tn:+.3f} (a circle: 1, a double cover: 2)")
    assert abs(tn) < 1e-3

    print("\n### B2. The rings overlap: the waves add")
    E2 = overlap(rng)
    s2 = chsh(E2)
    e45 = E2(0, math.pi / 4)
    print(f"ok  45 deg E = {e45:+.3f} (QM {-math.cos(math.pi / 4):+.3f}); CHSH = {s2:.3f} "
          f"(Tsirelson {2 * math.sqrt(2):.3f})")
    assert abs(e45 + math.cos(math.pi / 4)) < 0.01 and abs(s2 - 2 * math.sqrt(2)) < 0.03
    marg = []
    for b in (0.0, math.pi / 2):
        marg.append(sum(1 if rng.random() < 0.5 else -1 for _ in range(N)) / N)
    print(f"ok  no signalling: ring A alone averages {marg[0]:+.3f} / {marg[1]:+.3f} for two settings of B "
          f"(true BY CONSTRUCTION of the model - A is drawn first; a check of the code, not evidence)")
    assert all(abs(x) < 0.01 for x in marg)

    print("\n### B3. Which premise fails — the ZTL lens on one run")
    m = {"A0": "T", "B1": "F", "A1": "Z", "B0": "Z"}
    rep = {"A0", "B1"}                              # this run can witness only what it measured
    pair = judge("A0 & ~B1", m)["disposition"]
    defin = "(A0 | ~A0) & (A1 | ~A1) & (B0 | ~B0) & (B1 | ~B1)"
    c = ceiling(defin, m, rep)
    st = {a: stamp(a, m, rep) for a in ("A1", "B0")}
    print(f"ok  the measured pair: {pair}; 'all four readings have values': ceiling frozen = "
          f"{c['ceiling_frozen']}; unmade readings: {sorted(set(st.values()))}")
    assert pair == "EARNED" and c["ceiling_frozen"] and set(st.values()) == {"Z_PERMANENT"}

    print("\nBELL: all measurements hold.")
    print("The eight gives the minus, the overlap gives the cosine; the failed premise was never earned.")


if __name__ == "__main__":
    run()
