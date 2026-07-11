# -*- coding: utf-8 -*-
"""
Единый регрессионный раннер ZTL: все стенды + Lean.
Выход 0 = всё зелёное. Ключевые маркеры проверяются по выводу.
"""

import subprocess
import sys

STANDS = [
    ("ztl.py",         ["аксиома NOT(Z) = F"]),
    ("audit.py",       ["Итого: живых 12, павших 14"]),
    ("entailment.py",  ["Итого правил: живых 12, павших 2"]),
    ("tableau.py",     ["решения совпали ВСЕ"]),
    ("quantifiers.py", ["UI-правило", "✗ ¬∃ ⊨ ∀¬"]),
    ("tableau_fo.py",  ["совпали ВСЕ"]),
    ("paradoxes.py",   ["Неподвижной точки нет"]),
    ("fixedpoint.py",  ["НЕмонотонен", "карантин: {λ}"]),
    ("expeditions.py", ["ГИПОТЕЗА ПОДТВЕРЖДЕНА ТОТАЛЬНО"]),
    ("crocodile.py",   ["СДЕЛКА НЕ ЗАСЛУЖИВАЕТ ИСТИНЫ"]),
    ("zsets.py",       ["склейка не заработана"]),
    ("reals.py",       ["апартность заработана за t=1"]),
    ("zfuncs.py",      ["даже id не сертифицируется"]),
    ("zarith.py",      ["ЗАРАБОТАННЫЙ ноль"]),
    ("zprob.py",       ["ZTL-вердикт: Z"]),
    ("zmodal.py",      ["порог совпал"]),
    ("zrussell.py",    ["заземлено фактов: 8 из 9"]),
    ("zverify.py",     ["расхождений: 0", "нарушений монотонности стабильных вердиктов: 0"]),
    ("zcombine.py",    ["✓ на всех случаях"]),
]


def main():
    failures = []
    for script, markers in STANDS:
        r = subprocess.run([sys.executable, script],
                           capture_output=True, text=True, timeout=300)
        missing = [m for m in markers if m not in r.stdout]
        status = "OK " if r.returncode == 0 and not missing else "FAIL"
        print(f"  [{status}] {script}"
              + (f"  — нет маркеров: {missing}" if missing else "")
              + (f"  — код {r.returncode}" if r.returncode else ""))
        if status == "FAIL":
            failures.append(script)

    print("  [....] lean: lake build ...")
    r = subprocess.run(["lake", "build"], cwd="lean",
                       capture_output=True, text=True, timeout=900)
    lean_ok = r.returncode == 0 and \
        "does not depend on any axioms" in r.stdout + r.stderr
    print(f"  [{'OK ' if lean_ok else 'FAIL'}] lean (ноль аксиом: "
          f"{'подтверждён' if lean_ok else 'НЕ ПОДТВЕРЖДЁН'})")
    if not lean_ok:
        failures.append("lean")

    print()
    if failures:
        print(f"КРАСНОЕ: {failures}")
        return 1
    print(f"ВСЁ ЗЕЛЁНОЕ: {len(STANDS)} стендов + Lean.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
