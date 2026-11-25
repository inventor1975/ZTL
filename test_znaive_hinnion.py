# -*- coding: utf-8 -*-
"""Hinnion's refutation of EXT in Gilmore's partial set theory (RML 42, 2007, p. 50), replayed in ZTL's naive sets.

In PST+ the terms ρ = {x | x ∉ x}, φ = {x | ρ ∈ ρ} (the "double empty set"), τ(t) = {x | t ∈ x} and
τ* = {t | τ(t) ∩ φ = τ(t)} give a contradiction ONCE EXT identifies two-sided coextensive sets as objects:
τ(τ*) ≐ τ(τ*) ∩ φ ⇒ (EXT) τ(τ*) = τ(τ*) ∩ φ ⇒ τ* ∈ τ* ⇒ φ ∈ τ(τ*), against φ's emptiness.

In ZTL (2026-11-25): one cell is the source — ρ∈ρ, passport PARADOX; every other cell is DOWNSTREAM. The EXT
premise τ(τ*) ≐ τ(τ*) ∩ φ is NOT earned (OPEN): in PST+ "φ is double empty" is a proved fact (the gap counts as
knowledge), in ZTL φ's cells are unverified, so no identity is earned over them and the argument stops there.
znaive's identity is earned only on sets that decide every probe — Hinnion's EXT_Cl, which he shows consistent.
A finite universe (five names): a demonstration of the mechanism, not a consistency proof of the infinite theory.
"""
import sys

import znaive

U = {"sets": {
    "rho": {"abs": ["not", ["in", "x", "x"]]},
    "phi": {"abs": ["in", "rho", "rho"]},
    "tau_star": {"abs": ["all", "z", ["iff", ["and", ["in", "x", "z"], ["in", "z", "phi"]], ["in", "x", "z"]]]},
    "tau_ts": {"abs": ["in", "tau_star", "x"]},
    "meet_ts": {"abs": ["and", ["in", "tau_star", "x"], ["in", "x", "phi"]]}}}

checks = fails = 0


def ok(cond, what):
    global checks, fails
    checks += 1
    if not cond:
        fails += 1
        print("FAIL", what)


a = znaive.analyse(U)
_, _, _, kind = a
ok(kind["rho∈rho"] == "PARADOX", "the source is Russell's cell, a PARADOX")
ok(all(k == "DOWNSTREAM" for c, k in kind.items() if c != "rho∈rho"), "every other cell inherits the quarantine")
ok(znaive.judge_claim(a, ["eq", "tau_ts", "meet_ts"])["disposition"] == "OPEN", "the EXT premise is not earned")
ok(znaive.judge_claim(a, ["all", "y", ["not", ["in", "y", "phi"]]])["disposition"] == "OPEN",
   "'φ has no members' is not a theorem here (in PST+ it is)")
ok(znaive.judge_claim(a, ["in", "tau_star", "tau_star"])["disposition"] == "OPEN", "τ* ∈ τ* is not forced")
# the identity of znaive: earned only on decided probes (EXT_Cl); F against Z, and Z against Z, not identified
C = {"sets": {"a": {"list": ["a"]}, "b": {"list": ["a"]}, "p": {"data": {"a": "Z"}}, "q": {"data": {"a": "Z"}},
              "r": {"data": {"a": "F"}}}}
c = znaive.analyse(C)
for claim, want in ((["eq", "a", "b"], "EARNED"), (["eq", "r", "p"], "OPEN"), (["eq", "p", "q"], "OPEN"),
                    (["eq", "a", "r"], "REFUTED")):
    ok(znaive.judge_claim(c, claim)["disposition"] == want, f"{claim} -> {want}")
print(f"ZNAIVE HINNION GREEN — {checks} checks" if not fails else f"ZNAIVE HINNION RED: {fails} of {checks}")
sys.exit(1 if fails else 0)
