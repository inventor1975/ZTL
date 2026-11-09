# -*- coding: utf-8 -*-
"""Stand: zdiagnose — which premise is suspect when a measurement refutes a stated law with stated inputs
(2026-11-09). Both sides: a measurement INSIDE the stated range gives no conflict (no false suspicion); one outside
gives proved conflicts; zbackward's diagnoses equal the minimal hitting sets; a real case (ztl-stand physics round 2,
disc B, thin plate 7 % high) names the LAW as the only single-premise diagnosis."""
import sys

import zdiagnose as D

ok = fail = 0


def check(cond, what):
    global ok, fail
    if cond:
        ok += 1; print("  ok  ", what)
    else:
        fail += 1; print("  FAIL", what)


P = {"a": ((1, 1.1), (0.5, 2)), "b": ((2, 2.2), (1, 4))}
r = D.diagnose("a*b", P, (2.1, 2.2))
check(r["consistent_as_stated"] and r["conflicts"] == [], "a·b in [2, 2.42], measured 2.1–2.2: consistent, no suspect")
r = D.diagnose("a*b", P, (3.0, 3.1))
check(not r["consistent_as_stated"] and r["conflicts"] == [("a", "b", "law")],
      "measured 3.0–3.1 (above 2.42): one conflict {a, b, law} — each alone relaxed reaches it")
check(r["diagnoses"] == [("a",), ("b",), ("law",)] and r["check"].startswith("zbackward =="),
      "diagnoses {a} | {b} | {law}, zbackward equal to the minimal hitting sets")
P2 = {"a": ((1, 1.1), (1, 1.2)), "b": ((2, 2.2), (2, 2.3))}
r = D.diagnose("a*b", P2, (3.0, 3.1), law_relaxed=(0.5, 2))
check(r["diagnoses"] == [("law",)], "a·b with tight relaxations (≤ 2.76 < 3.0): only the LAW can be the culprit")

expr = "l2/(2*pi*(dd/2)*(dd/2))*tt*sqrt(E/(r*(1 - nu*nu)))/sqrt(12)"
d, t, rho, f = 48.00, 6.581, 2725, 13728.9
PB = {"l2": ((5.196, 5.26), (5.13, 5.36)), "E": ((68e9, 70e9), (66e9, 74e9)), "nu": ((0.33, 0.35), (0.30, 0.36)),
      "dd": (((d - 0.1) / 1e3, (d + 0.1) / 1e3), ((d - 0.5) / 1e3, (d + 0.5) / 1e3)),
      "tt": (((t - 0.01) / 1e3, (t + 0.01) / 1e3), ((t - 0.05) / 1e3, (t + 0.05) / 1e3)),
      "r": ((rho * 0.995, rho * 1.005), (rho * 0.97, rho * 1.03))}
r = D.diagnose(expr, PB, (f * 0.9985, f * 1.0015))
singles = [x for x in r["diagnoses"] if len(x) == 1]
check(singles == [("law",)] and r["check"].startswith("zbackward =="),
      "disc B (thin plate 7 % above the measurement): the only single-premise diagnosis is the LAW")

print(f"\n{ok} ok, {fail} fail")
print("ZDIAGNOSE GREEN" if fail == 0 else "ZDIAGNOSE RED")
sys.exit(1 if fail else 0)
