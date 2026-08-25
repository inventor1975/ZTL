#!/usr/bin/env python3
"""Надёжный источник правды по таблицам и операторам ZTL.

Всё считается из ztl.py; глазам верить не надо. По слову куратора
(2026-08-22): «ты бы скриптом сделал — было бы надёжно».

    ./ztl_tables.py            полный отчёт: инвентарь + все таблицы
    ./ztl_tables.py --check    только проверки; выход != 0, если что-то не так
    ./ztl_tables.py --json     данные для генераторов картинок / контрольных

Что проверяется:
  * порождающий принцип воспроизводит опорные клетки (аксиомы ztl.py);
  * среди 16 бинарных функций РОВНО 10 зависят от обоих входов;
  * жадный (наш) и терпеливый (супероценка) расходятся только там, где
    терпеливый молчит (Z), а жадный схлопывает — и нигде больше.
"""
import itertools, json, sys, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import ztl

T, F, Z = ztl.T, ztl.F, ztl.Z
V = [T, F, Z]
NM = {T: "T", F: "F", Z: "Z"}
subs = lambda x: [x] if x in (T, F) else [T, F]

NOT, AND, OR, IMP, XOR, XNOR = ztl.NOT, ztl.AND, ztl.OR, ztl.IMP, ztl.XOR, ztl.XNOR

# --- терпеливый (супероценка): молчит, где доигрывания расходятся ---
def patient2(cl, a, b):
    o = {cl(x, y) for x in subs(a) for y in subs(b)}
    return T if o == {T} else F if o == {F} else Z
def patient1(cl, a):
    o = {cl(x) for x in subs(a)}
    return T if o == {T} else F if o == {F} else Z

# классические ядра
cnot = lambda a: F if a == T else T
cand = lambda a, b: T if a == T and b == T else F
cor = lambda a, b: T if a == T or b == T else F
cimp = lambda a, b: T if a == F or b == T else F
cconv = lambda a, b: T if b == F or a == T else F      # a<-b = b->a
cxor = lambda a, b: T if a != b else F
cxnor = lambda a, b: T if a == b else F

# наши рабочие связки: (подпись, классическое ядро, ЖАДНАЯ реализация из ztl.py)
UNARY = ("¬", cnot, NOT)
BINARY = [
    ("∧",  cand,  AND),
    ("∨",  cor,   OR),
    ("→",  cimp,  IMP),
    ("↔",  cxnor, XNOR),
    ("⊕",  cxor,  XOR),
    ("¬(a∧b)", lambda a, b: cnot(cand(a, b)), lambda a, b: NOT(AND(a, b))),
    ("¬(a∨b)", lambda a, b: cnot(cor(a, b)),  lambda a, b: NOT(OR(a, b))),
    ("¬(a⊕b)", lambda a, b: cnot(cxor(a, b)), lambda a, b: NOT(XOR(a, b))),
    ("¬(a→b)", lambda a, b: cnot(cimp(a, b)), lambda a, b: NOT(IMP(a, b))),
]

def table(fn2):
    return [[NM[fn2(a, b)] for b in V] for a in V]

def collapse_cells(greedy, cl):
    return [(NM[a], NM[b]) for a in V for b in V if greedy(a, b) != patient2(cl, a, b)]

# --- инвентарь всех 16 бинарных функций ---
def inventory():
    inp = [(T, T), (T, F), (F, T), (F, F)]
    genuine, other = [], []
    for bits in itertools.product((T, F), repeat=4):
        d = dict(zip(inp, bits))
        cl = lambda a, b, d=d: d[(a, b)]
        da = any(cl(T, b) != cl(F, b) for b in (T, F))
        db = any(cl(a, T) != cl(a, F) for a in (T, F))
        (genuine if (da and db) else other).append("".join(NM[x] for x in bits))
    return genuine, other

def check():
    bad = []
    # 1. опорные клетки
    _, anchor_bad = ztl.tests_axioms()
    if anchor_bad:
        bad.append(f"опорные клетки не воспроизводятся: {anchor_bad}")
    # 2. ровно 10 настоящих бинарных
    genuine, _ = inventory()
    if len(genuine) != 10:
        bad.append(f"настоящих бинарных не 10, а {len(genuine)}")
    # 3. жадный и терпеливый расходятся только по схлопыванию (жадный != Z)
    for sign, cl, greedy in BINARY:
        for a in V:
            for b in V:
                g, p = greedy(a, b), patient2(cl, a, b)
                if g != p and not (p == Z and g in (T, F)):
                    bad.append(f"{sign}: неожиданное расхождение на {NM[a]}{NM[b]}: жадный {NM[g]}, терпеливый {NM[p]}")
    # 4. никакого Z в теле жадных таблиц
    for sign, cl, greedy in BINARY:
        if any(greedy(a, b) == Z for a in V for b in V):
            bad.append(f"{sign}: третий знак Z просочился в тело жадной таблицы")
    return bad

def as_json():
    genuine, other = inventory()
    data = {
        "unary": {"sign": UNARY[0],
                  "greedy": [NM[NOT(a)] for a in V],
                  "patient": [NM[patient1(cnot, a)] for a in V]},
        "binary": [], "inventory": {"genuine_both": genuine, "not_both": other,
                                    "genuine_count": len(genuine)},
    }
    for sign, cl, greedy in BINARY:
        data["binary"].append({
            "sign": sign, "greedy": table(greedy),
            "patient": [[NM[patient2(cl, a, b)] for b in V] for a in V],
            "collapse_cells": collapse_cells(greedy, cl),
        })
    return data

def report():
    genuine, other = inventory()
    print("ИНВЕНТАРЬ 16 БИНАРНЫХ ФУНКЦИЙ")
    print(f"  зависят от обоих входа (настоящие бинарные): {len(genuine)}")
    print(f"  константы и проекции (не оба):               {len(other)}")
    print()
    print("УНАРНЫЙ  ¬       жадный", [NM[NOT(a)] for a in V],
          " терпеливый", [NM[patient1(cnot, a)] for a in V])
    print()
    print("НАШИ 9 РАБОЧИХ БИНАРНЫХ  (жадный | терпеливый | клетки схлопывания)")
    for sign, cl, greedy in BINARY:
        g = table(greedy)
        p = [[NM[patient2(cl, a, b)] for b in V] for a in V]
        cc = collapse_cells(greedy, cl)
        print(f"\n  {sign}")
        for i, a in enumerate(V):
            print(f"    {NM[a]}  {g[i]}   |   {p[i]}")
        print(f"    схлопнуто: {len(cc)}  {cc}")
    print("\nПРОВЕРКИ")
    bad = check()
    if bad:
        for b in bad:
            print("  ✗", b)
    else:
        print("  ✓ всё сходится: опоры воспроизведены, настоящих бинарных 10,")
        print("    расхождения только по схлопыванию молчания, Z в тело не течёт.")
    return bad

if __name__ == "__main__":
    if "--json" in sys.argv:
        print(json.dumps(as_json(), ensure_ascii=False, indent=2))
    elif "--check" in sys.argv:
        sys.exit(1 if check() else 0)
    else:
        sys.exit(1 if report() else 0)
