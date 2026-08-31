# -*- coding: utf-8 -*-
"""AIRLINE-PILOT-001: перепись ПРЕДИКАТОВ в остальных правилах политики.

УРОВЕНЬ ЗАМЕРА НАЗВАН ВСЛУХ: это ЧУВСТВИТЕЛЬНОСТЬ ПРЕДИКАТА — «изменит ли
исход этого атома последствие». Это НЕ действие приобретения. Один вызов
`get_reservation_details` открывает разом класс, страховку, сегменты и
маршрут, поэтому снятие одного предиката может не сэкономить НИ ОДНОГО
вызова. Действенный потолок здесь не считается и за него не выдаётся.

ПРАВИЛА, дословно из wiki_airline.md (sha256 56c33580…):

  ИЗМЕНЕНИЕ РЕЙСОВ (строка 44):
    «Basic economy flights cannot be modified. Other reservations can be
     modified without changing the origin, destination, and trip type.»
      modify_allowed = (не basic_economy) И тот_же_origin И тот_же_dest
                       И тот_же_тип_поездки

  СМЕНА КЛАССА (строка 46): разрешена ВСЕМ, включая basic economy, но требует
    доплаты разницы и единого класса на все сегменты.
      cabin_change_allowed = единый_класс_на_все_сегменты
    (класс брони НЕ участвует — источник говорит «all reservations»)

  БАГАЖ ПРИ ИЗМЕНЕНИИ (строка 48): добавлять можно, убирать нельзя.
      baggage_change_allowed = не_уменьшение

  ПАССАЖИРЫ (строка 50): менять можно, ЧИСЛО менять нельзя.
      passenger_change_allowed = то_же_число

  КОМПЕНСАЦИЯ (строки 66-70):
    «If the user is silver/gold member or has travel insurance or flies
     business, and complains about cancelled flights … $100 times passengers»
      compensation_allowed = (silver_gold ИЛИ insurance ИЛИ business)
                             И пожаловался И попросил_явно
"""
import itertools, sys
from collections import Counter

RULES = {
    "изменение рейсов": (
        ["не_basic_economy", "тот_же_origin", "тот_же_dest", "тот_же_тип"],
        lambda v: (v["не_basic_economy"] and v["тот_же_origin"]
                   and v["тот_же_dest"] and v["тот_же_тип"]),
        None),
    "смена класса": (
        ["единый_класс_на_сегментах"],
        lambda v: v["единый_класс_на_сегментах"],
        None),
    "багаж при изменении": (
        ["не_уменьшение"],
        lambda v: v["не_уменьшение"],
        None),
    "пассажиры": (
        ["то_же_число"],
        lambda v: v["то_же_число"],
        None),
    "компенсация": (
        ["silver_gold", "insurance", "business", "пожаловался", "попросил"],
        lambda v: ((v["silver_gold"] or v["insurance"] or v["business"])
                   and v["пожаловался"] and v["попросил"]),
        # Допустимость: источник не запрещает никаких сочетаний этих пяти.
        # Класс и уровень независимы (промерено по базе для отмены).
        None),
}


def sensitivity(preds, rule, admissible=None):
    out = {}
    for c in preds:
        free = [p for p in preds if p != c]
        branch = {}
        for val in (True, False):
            vs = set()
            for combo in itertools.product([True, False], repeat=len(free)):
                v = {c: val}; v.update(dict(zip(free, combo)))
                if admissible and not admissible(v):
                    continue
                vs.add(rule(v))
            branch[val] = vs
        allv = branch[True] | branch[False]
        if branch[True] == branch[False] and len(allv) == 1:
            out[c] = "SETTLES"
        else:
            out[c] = "MOVES"
    return out


def main():
    print("=" * 66)
    print("AIRLINE-PILOT-001 — чувствительность ПРЕДИКАТОВ, остальные правила")
    print("=" * 66)
    print("\nУРОВЕНЬ: чувствительность предиката. НЕ действие приобретения.")
    tally = Counter()
    for name, (preds, rule, adm) in RULES.items():
        res = sensitivity(preds, rule, adm)
        tally.update(res.values())
        print(f"\n  {name} ({len(preds)} предикатов):")
        for p, k in res.items():
            print(f"    {p:<28} {k}")
    print("\n" + "=" * 66)
    tot = sum(tally.values())
    print(f"ИТОГ по этим правилам: предикатов {tot}, "
          f"SETTLES {tally['SETTLES']}, MOVES {tally['MOVES']}")
    print("\nКОНТРОЛЬ, что прибор ВООБЩЕ умеет находить SETTLES:")
    ctl = sensitivity(["a", "b"], lambda v: True)   # вердикт не зависит ни от чего
    print(f"  правило-константа: {ctl} — обе обязаны быть SETTLES")
    if set(ctl.values()) != {"SETTLES"}:
        print("  КОНТРОЛЬ ПРОВАЛЕН: прибор не находит заведомый SETTLES.")
        return 1
    print("  контроль пройден.")
    print("\nПОТОЛОК: это ЛОГИЧЕСКАЯ чувствительность. Действенная экономия")
    print("не измерена: один вызов открывает несколько полей сразу.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
