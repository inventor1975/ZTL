# -*- coding: utf-8 -*-
"""
Zeno's Achilles and Gabriel's horn, judged: a process with infinitely many stages, and the object it converges to.

  ACHILLES  (Aristotle, Physics VI.9) Achilles runs ten times faster than the tortoise, which starts 1 ahead. When
            he reaches where it was, it has moved on; and so on forever — so he never catches it.
  GABRIEL'S HORN  (Torricelli, 1643) y = 1/x for x >= 1, turned about the axis: finite volume (pi), infinite
            surface. "You can fill it with paint but never paint it."

THE FORMALISATION, IN WORDS FIRST — the same two objects as 0.999... (dilemmas/point_nine.py):
  ACHILLES  the STAGES: at every stage he is still behind — true of each stage; the MOTION: positions are a function
            of time, and at t = 1/9 he is level — true of the motion. "He never catches it" is true of the stages and
            false of the motion; the stage times sum to exactly 1/9.
  HORN      "a coat of paint of thickness t over the inner surface" names nothing: the horn's radius 1/x falls below t
            beyond x = 1/t, where no layer of thickness t fits inside — the description has no subject (E). Filling
            the horn is not painting it with any positive thickness; with thickness 0 no paint is needed at all.

MEASURED HERE:
  1. Achilles: the k-th stage time is (1/10)^k (speed 10, gap 10^-(k-1)... scaled: gap 1, speed 10 vs 1); every
     partial sum is below 1/9, exactly, and they come within 10^-60 of it; at t = 1/9 the positions coincide
     (10 t = 1 + t), exactly;
  2. the horn: the volume to R is pi (1 - 1/R) -> pi; the surface to R exceeds 2 pi ln R -> infinity (both from the
     closed forms; at R = 10 and 10^3 also by numerical integration, within 1e-6 relative);
  3. "a coat of thickness t over the whole inner surface": for t = 0.1, 0.01, 0.001 the radius drops below t at
     x = 1/t — the coat has no room there; the claim is E (computed: the room vanishes), not "true but needs
     infinite paint".
Run:  python3 dilemmas/zeno.py
"""
import math
import os
import sys
from fractions import Fraction as Fr

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from ztljudge import judge                                    # noqa: E402


def integrate(f, a, b, n=200_000):
    h = (b - a) / n                                          # Simpson's rule (the numerical method), n even
    s = f(a) + f(b) + sum((4 if i % 2 else 2) * f(a + i * h) for i in range(1, n))
    return s * h / 3


if __name__ == "__main__":
    print("-" * 72)
    print("1. ACHILLES: EVERY STAGE BEHIND, THE MOTION LEVEL AT t = 1/9")
    total, catch, behind = Fr(0), Fr(1, 9), True
    for k in range(1, 61):
        total += Fr(1, 10 ** k)          # stage k: Achilles covers the gap 10^-(k-1) at speed 10, in time 10^-k
        behind = behind and total < catch
    assert catch - total < Fr(1, 10 ** 60)
    assert 10 * catch == 1 + catch
    assert behind
    stages = judge("behind_at_every_stage", {"behind_at_every_stage": "T" if behind else "F"})
    motion = judge("never_catches", {"never_catches": "F" if 10 * catch == 1 + catch else "T"})
    print(f"   60 stages: total time {float(total):.12f} < 1/9; at t = 1/9: 10t = 1 + t")
    print(f"   'behind at every stage': {stages['disposition']};  'never catches him' (of the motion): {motion['disposition']}")
    print("-" * 72)
    print("2. THE HORN: FINITE VOLUME, INFINITE SURFACE")
    for R in (10.0, 1e3, 1e6):
        vol = integrate(lambda x: math.pi / x ** 2, 1.0, R) if R <= 1e3 else math.pi * (1 - 1 / R)
        assert abs(vol - math.pi * (1 - 1 / R)) < 1e-6 * math.pi
        area_lb = 2 * math.pi * math.log(R)
        area = integrate(lambda x: 2 * math.pi / x * math.sqrt(1 + 1 / x ** 4), 1.0, R) if R <= 1e3 else area_lb
        assert area >= area_lb - 1e-6
        print(f"   to R = {R:9.0f}: volume {vol:.6f} (-> pi)   surface >= {area_lb:.3f} (-> infinity)")
    print("-" * 72)
    print("3. 'A COAT OF THICKNESS t OVER THE INNER SURFACE'")
    for t in (0.1, 0.01, 0.001):
        x_out = 1 / t                                        # radius 1/x < t beyond here: no room for the coat
        assert 1 / (x_out * 1.0001) < t
        room = "E" if 1 / (x_out * 1.0001) < t else "T"     # computed: the coat has no room past x = 1/t
        r = judge("coat_of_thickness_t", {"coat_of_thickness_t": room})
        assert r["disposition"] == "E"
        print(f"   t = {t}: the radius falls below t at x = {x_out:.0f}; the coat: {r['disposition']} (no room — no subject)")
    print("   Filling the horn is not painting it at any positive thickness.")
    print("-" * 72)
    print("ZENO AND THE HORN: all measurements hold.")
