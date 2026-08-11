# -*- coding: utf-8 -*-
"""znumride — the claims-sheet judge ridden against PREDICTED verdicts.

The other stands check the instrument against its own examples. This one
checks it against invented traps whose verdict is written down BEFORE the
run: parenthesised comparisons, empty domains, composed units, division
through zero, decorrelated occurrences, two lattices for one half, kopeck
arithmetic. A mismatch is a finding — in the instrument or in the author's
head, and either is worth the run. It found two on its first ride
(2026-08-11): '~(a == b)' and '(x > 10) ^ ok' would not parse at all.

Run:  python3 znumride.py
"""
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from znumjudge import judge_sheet_claim, parse_quantities  # noqa: E402

# (label, formula, quantities, expected disposition | "ERROR:<code>", cures)
CASES = [
    ("стрелка_не_сравнение", "4 > 3 -> 5 > 3", "",
     "EARNED", []),
    ("декорреляция", "m - m == 0", "m=[0,9] earned:sensor",
     "OPEN", ["measure m"]),
    ("половина_двумя_решётками", "a == b",
     "a=0.5 decimal1 earned:x, b=1/2 frac2 earned:y",
     "EARNED", []),
    ("пустой_домен", "k >= 1", "k=[0.2,0.9] int credit",
     "ERROR:E_EMPTY_DOMAIN", []),
    ("составная_единица", "speed == dist / time",
     "speed=[50,60] credit km/h, dist=110 earned:odo km, time=2 earned:clock h",
     "OPEN", ["measure speed", "document speed"]),
    ("единицы_умножения", "area == w * h",
     "area=6 earned:doc m2, w=2 earned:t m, h=3 earned:t m",
     "ERROR:E_UNIT", []),
    ("двое_в_кредит", "x <= y", "x=[0,1] credit, y=[5,6] credit",
     "ON CREDIT", ["document x", "document y"]),
    ("делитель_через_ноль", "n / d < 10", "n=5 earned:doc, d=[-1,1] earned:doc",
     "OPEN", ["measure d"]),
    ("чистое_опровержение", "n == 7", "n=8 earned:doc int",
     "REFUTED", []),
    ("отрицание_на_кредите", "~(a == b)", "a=50 earned:log, b=70 credit",
     "ON CREDIT", ["document b"]),
    ("исключающее_или", "(x > 10) ^ ok", "x=[20,30] earned:m, ok=F",
     "EARNED", []),
    ("копейки_с_умножением", "sum(a,b,c) * 2 <= budget",
     "a=1.05 decimal2 earned:i1, b=2.15 decimal2 earned:i2, "
     "c=0.80 decimal2 earned:i3, budget=8.00 decimal2 earned:o1",
     "EARNED", []),
]

bad = 0
for label, formula, data, want_disp, want_cures in CASES:
    try:
        quantities, marks = parse_quantities(data)
        r = judge_sheet_claim(formula, quantities, marks)
        got_disp = r["disposition"] + (f" ({r['polarity']})" if r["polarity"] else "")
        got_cures = r["next_check"]
    except Exception as e:
        got_disp = f"ERROR:{str(e).split(':')[0]}"
        got_cures = []
    ok = got_disp.split(" (")[0] == want_disp and got_cures == want_cures
    bad += not ok
    print(f"  {'ok  ' if ok else 'РАЗОШЛОСЬ'} [{label}] {formula}")
    if not ok:
        print(f"        ждал: {want_disp} {want_cures}")
        print(f"        дал:  {got_disp} {got_cures}")

print(f"\n  расхождений: {bad} из {len(CASES)}")
assert bad == 0, "a predicted verdict and the machine's disagree — read both"
print("ZNUMRIDE GREEN — every predicted verdict met the machine's")
