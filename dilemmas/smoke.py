# -*- coding: utf-8 -*-
"""smoke — "no smoke without fire": the street version of the day's machine.

Atoms: s = smoke (the rumour — observed), f = fire (the guilt — hidden).
The proverb turns evidence into a verdict: the rumour exists, so the
guilt is real. Run, not argued.
"""
import os
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)
sys.path.insert(0, os.path.join(_ROOT, "zhunt"))

from zhunt import judge

LAW = ("imp", ("not", "f"), ("not", "s"))          # "no smoke without fire"
INF = ("imp", ("and", LAW, "s"), "f")              # smoke, therefore fire


def run():
    v_inf = judge(INF, {"f": "M", "s": "T"})
    v_law = judge(LAW, {"f": "M", "s": "T"})
    v_f = judge("f", {"f": "M"})
    print("NO SMOKE WITHOUT FIRE — through the core\n")
    print(f"  the inference ((¬f→¬s)∧s)→f → {v_inf[0]}, {v_inf[1]}")
    print(f"  the law ¬f→¬s at smoke s=T  → {v_law[0]}, {v_law[1]}, "
          f"killed by f:={v_law[2]['f']}")
    print(f"  the verdict f under smoke   → {v_f[0]}, {v_f[1]}")
    assert v_inf[:2] == ("F", "until-verification")
    assert v_law[:2] == ("T", "until-verification") and v_law[2] == {"f": "F"}
    assert v_f[:2] == ("Z", "until-verification")
    print("\n  worse than Job's friends: THERE the inference frame was honest")
    print("  and only the fuel was credit — HERE the inference itself rides")
    print("  the fallen direction of contraposition. The law's counter-cell")
    print("  is f:=F — smoke without fire exists, the smoke MACHINE makes it")
    print("  (slander manufactures smoke cheaply; fire it cannot make).")
    print("  Smoke is a MARK — an order to verify (Проверяй!) — and the")
    print("  proverb sells the mark as a verdict.")


if __name__ == "__main__":
    run()
