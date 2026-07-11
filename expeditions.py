# -*- coding: utf-8 -*-
"""
Экспедиции в открытый океан: Карри, теорема чётности, Ябло.

Приборы — из fixedpoint.py (жадный/ленивый скачки, неподвижные точки).

Э1. КАРРИ: c = (Tr(c) → ⊥). Взрывается без отрицания — ломает многие
    параконсистентные подходы. Вопрос: гасит ли его наш карантин той же
    механикой, что лжеца?
Э2. ЧЁТНОСТЬ: цикл s₀→s₁→…→s₀, каждое ребро — «копировать» или
    «инвертировать». Гипотеза (XOR-бухгалтер): классические модели
    существуют ⟺ число инверсий чётно. Тотальная проверка: все циклы
    длины 1–5, все узоры инверсий.
Э3. ЯБЛО: sᵢ = «все следующие ложны» (без единого цикла!). Бесконечная
    версия парадоксальна; что видят конечные обрезки?
"""

from itertools import product

from ztl import T, F, Z, VALUES
from fixedpoint import (EAGER, LAZY, fixed_points, iterate, least_fp_lazy,
                        jump, ev_reg, fmt_v)


def expedition_curry():
    print("### Э1. КАРРИ: c = (Tr(c) → ⊥)")
    system = {"c": ("imp", "c", "F")}
    fe = fixed_points(system, EAGER)
    fl = fixed_points(system, LAZY)
    print(f"  жадные неподвижные точки: {', '.join(map(fmt_v, fe)) or 'НЕТ'}")
    print(f"  ленивые неподвижные точки: {', '.join(map(fmt_v, fl)) or 'НЕТ'}")
    trace, loop = iterate(system, EAGER)
    period = len(trace) - loop if loop is not None else None
    cyc = " → ".join(fmt_v(v) for v in trace[loop:]) if period and period > 1 else ""
    print(f"  жадная итерация из Z: {'ЦИКЛ периода ' + str(period) + ': ' + cyc if period and period > 1 else 'сошлась'}")
    lfp = least_fp_lazy(system)
    print(f"  ленивое заземление: {fmt_v(lfp)} — карантин: "
          f"{[k for k, v in lfp.items() if v == Z] or 'пуст'}")
    content = ev_reg(system["c"], lfp, EAGER)
    print(f"  жадный вердикт по содержанию c: {content}")
    print("  Вывод: Карри бездомен жадно и заземлён лениво — ТА ЖЕ механика,")
    print("  что у лжеца, хотя отрицания в нём нет: карантину всё равно,")
    print("  каким оператором предложение развернуло само себя.")


def cycle_system(pattern):
    """Цикл: s_i определено через s_{i+1 mod n}; pattern[i]=1 — инверсия."""
    n = len(pattern)
    sys_ = {}
    for i, inv in enumerate(pattern):
        ref = f"s{(i + 1) % n}"
        sys_[f"s{i}"] = ("not", ref) if inv else ref
    return sys_


def expedition_parity(max_n=5):
    print("\n### Э2. ТЕОРЕМА ЧЁТНОСТИ: все циклы длины 1..%d, все узоры" % max_n)
    checked = bad = 0
    for n in range(1, max_n + 1):
        for pattern in product((0, 1), repeat=n):
            system = cycle_system(pattern)
            classical = [v for v in fixed_points(system, EAGER)
                         if all(x in (T, F) for x in v.values())]
            even = sum(pattern) % 2 == 0
            checked += 1
            if bool(classical) != even:
                bad += 1
                print(f"  ✗ n={n} узор={pattern}: инверсий {sum(pattern)}, "
                      f"классических моделей {len(classical)}")
    print(f"  проверено циклов: {checked}")
    if not bad:
        print("  ✓ ГИПОТЕЗА ПОДТВЕРЖДЕНА ТОТАЛЬНО: классические модели")
        print("    существуют ⟺ число инверсий по кольцу чётно (XOR-сумма 0).")
        print("    Нечётные кольца — карусели (лжец n=1, Журден n=2, ...);")
        print("    чётные — правдолюбы (недоопределённость, не парадокс).")
    return checked, bad


def yablo_system(n):
    """Обрезка Ябло: s_i = ⋀_{j>i} ¬Tr(s_j); последний — пустая конъюнкция T."""
    sys_ = {}
    for i in range(n):
        parts = [("not", f"s{j}") for j in range(i + 1, n)]
        if not parts:
            phi = "T"
        else:
            phi = parts[0]
            for p in parts[1:]:
                phi = ("and", phi, p)
        sys_[f"s{i}"] = phi
    return sys_


def expedition_yablo(max_n=6):
    print("\n### Э3. ЯБЛО (обрезки): s_i = «все следующие ложны»")
    for n in range(2, max_n + 1):
        system = yablo_system(n)
        lfp = least_fp_lazy(system)
        quarantined = [k for k, v in lfp.items() if v == Z]
        fe = fixed_points(system, EAGER)
        vals = "".join(lfp[f"s{i}"] for i in range(n))
        print(f"  n={n}: заземление {vals} (слева s0), карантин "
              f"{quarantined or 'ПУСТ'}, жадных моделей {len(fe)}")
    print("  Вывод: КАЖДАЯ конечная обрезка полностью заземлена (последний")
    print("  истинен вакуумно, остальные ложны) — парадокса нет ни при каком n.")
    print("  Парадокс Ябло живёт ТОЛЬКО на актуальной бесконечности: в отличие")
    print("  от каруселей (конечных колец), его нельзя поймать конечным")
    print("  прибором — и нельзя обвинить в цикличности. Бесконечный регресс —")
    print("  самостоятельный, третий источник незаземлённости.")


if __name__ == "__main__":
    print("=" * 72)
    print("ЭКСПЕДИЦИИ: КАРРИ, ЧЁТНОСТЬ, ЯБЛО")
    print("=" * 72)
    expedition_curry()
    expedition_parity()
    expedition_yablo()
