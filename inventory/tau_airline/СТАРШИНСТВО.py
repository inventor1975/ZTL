# -*- coding: utf-8 -*-
"""Старшинство разрядов, ЗАМОРОЖЕНО в коде — 2026-08-31.

Без старшинства «SETTLES» поглощает обычное сокращение всякий раз, когда
проверка функциональной инвариантности случайно вернула истину. Порядок:

  1. STATIC        — неуместен по источнику или структуре зависимостей,
                     ДО всяких наблюдений.
  2. SHORT-CIRCUIT — УЖЕ УСТАНОВЛЕННОЕ состояние фиксирует последствие
                     ДО этого дознания.
  3. SETTLES       — ни то ни другое, предикат не разрешён, но КАЖДОЕ
                     допустимое значение оставляет полное последствие тем же.
  4. MOVES         — остаётся способным изменить последствие, в том числе
                     во взаимодействии с прочими неразрешёнными.

НЕПУСТОТА: если при ограничениях задачи допустимо лишь ОДНО значение
предиката, это НЕ settles. Это связанный/статический факт, а не свидетельство
бесполезности проверки обоих исходов.
"""
import itertools


def classify(p, preds, rule, admissible=None, known=None, static=None):
    known = known or {}
    static = static or set()

    if p in static:
        return "STATIC"

    free = [q for q in preds if q != p and q not in known]

    # НЕПУСТОТА: оба значения p должны быть допустимы хоть при одном наборе
    both_live = False
    invariant = True
    for combo in itertools.product([True, False], repeat=len(free)):
        base = dict(known); base.update(dict(zip(free, combo)))
        vt = dict(base); vt[p] = True
        vf = dict(base); vf[p] = False
        if admissible and not (admissible(vt) and admissible(vf)):
            continue
        both_live = True
        if rule(vt) != rule(vf):
            invariant = False
            break
    if not both_live:
        return "STATIC"          # одно значение — связанный факт, не settles

    if not invariant:
        return "MOVES"

    # инвариантно. СОКРАЩЕНИЕ, если решило УЖЕ ИЗВЕСТНОЕ: проверяем, была бы
    # инвариантность и БЕЗ известных фактов. Если без них предикат двигал —
    # значит его убили наблюдения, и это сокращение, а не settles.
    if known:
        moved_without = False
        allfree = [q for q in preds if q != p]
        for combo in itertools.product([True, False], repeat=len(allfree)):
            base = dict(zip(allfree, combo))
            vt = dict(base); vt[p] = True
            vf = dict(base); vf[p] = False
            if admissible and not (admissible(vt) and admissible(vf)):
                continue
            if rule(vt) != rule(vf):
                moved_without = True
                break
        if moved_without:
            return "SHORT-CIRCUIT"
    return "SETTLES"


if __name__ == "__main__":
    P = ["p", "q"]
    rule = lambda v: v["p"] or v["q"]
    cases = [
        ("ничего не известно",            {},              "MOVES"),
        ("q установлено ИСТИНОЙ",         {"q": True},     "SHORT-CIRCUIT"),
        ("q установлено ЛОЖЬЮ",           {"q": False},    "MOVES"),
    ]
    fails = []
    print("СТАРШИНСТВО — стенд на p в правиле (p ИЛИ q):")
    for name, known, want in cases:
        got = classify("p", P, rule, known=known)
        ok = "ок" if got == want else "ПРОВАЛ"
        print(f"  {name:<28} -> {got:<14} (ждали {want}) {ok}")
        if got != want:
            fails.append(name)
    g = classify("p", P, rule, static={"p"})
    print(f"  объявлен статическим         -> {g:<14} (ждали STATIC) "
          f"{'ок' if g=='STATIC' else 'ПРОВАЛ'}")
    if g != "STATIC":
        fails.append("static")
    # непустота: допустимо только p=True
    g2 = classify("p", P, rule, admissible=lambda v: v["p"] is True)
    print(f"  допустимо лишь одно значение -> {g2:<14} (ждали STATIC) "
          f"{'ок' if g2=='STATIC' else 'ПРОВАЛ'}")
    if g2 != "STATIC":
        fails.append("непустота")
    print()
    if fails:
        print("СТАРШИНСТВО КРАСНОЕ:", fails)
        raise SystemExit(1)
    print("СТАРШИНСТВО ЗЕЛЁНОЕ — сокращение не поглощается settles,")
    print("и единственное допустимое значение не выдаётся за settles.")
