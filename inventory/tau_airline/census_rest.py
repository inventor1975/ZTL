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
    """ИСПРАВЛЕНО 2026-08-31 — прежнее определение было НЕВЕРНЫМ.

    Было: SETTLES, если множество вердиктов при T совпало с множеством при F
    И оказалось ОДНОЭЛЕМЕНТНЫМ. Второе требование лишнее и губительное: оно
    ловило только предикаты в ГЛОБАЛЬНО постоянных правилах. На контроле
    (a И b) ИЛИ (a И НЕ b) = a предикат b объявлялся MOVES, хотя изменить
    исход не может.

    Стало: SETTLES, если ПРИ КАЖДОМ допустимом наборе прочих смена этого
    предиката НЕ МЕНЯЕТ полного последствия. Это и есть «проверка бесполезна».

    Ошибка смещала в сторону MOVES, то есть в сторону меньшего числа SETTLES,
    то есть в сторону NO-GO — ровно туда, куда клонилась моя же рекомендация.
    """
    out = {}
    for c in preds:
        free = [p for p in preds if p != c]
        moves = False
        for combo in itertools.product([True, False], repeat=len(free)):
            base = dict(zip(free, combo))
            vt = dict(base); vt[c] = True
            vf = dict(base); vf[c] = False
            if admissible and not (admissible(vt) and admissible(vf)):
                continue          # пара недопустима — не голосует
            if rule(vt) != rule(vf):
                moves = True
                break
        out[c] = "MOVES" if moves else "SETTLES"
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
    # ТРИ КОНТРОЛЯ. Первый слишком лёгок сам по себе — внешний рецензент верно указал
    # 2026-08-31: правило-константа проверяет лишь, что прибор видит предикат
    # БЕЗ ВСЯКОГО влияния. Наша настоящая мишень труднее: предикат, который
    # В ПРАВИЛО ВХОДИТ, но обессмыслен избыточностью или доминированием.
    print("\nКОНТРОЛИ ПРИБОРА (три, от лёгкого к настоящему):")
    fails = []

    ctl1 = sensitivity(["a", "b"], lambda v: True)
    print(f"  1. правило-константа        : {ctl1}")
    if set(ctl1.values()) != {"SETTLES"}:
        fails.append("константа не дала SETTLES")

    # (a И b) ИЛИ (a И НЕ b) = a. Предикат b ВХОДИТ в правило и при этом
    # изменить исход не может. Это булева ИЗБЫТОЧНОСТЬ.
    ctl2 = sensitivity(["a", "b"],
                       lambda v: (v["a"] and v["b"]) or (v["a"] and not v["b"]))
    print(f"  2. булева избыточность      : {ctl2}")
    if ctl2.get("b") != "SETTLES":
        fails.append("избыточный b не опознан как SETTLES")
    if ctl2.get("a") != "MOVES":
        fails.append("несущий a ошибочно назван SETTLES")

    # ЧИСЛОВОЕ ДОМИНИРОВАНИЕ: построенный свидетель из багажной таблицы.
    # business, запрошено 2 места; нормы по уровням 2/3/3 — доплата ноль при
    # ЛЮБОМ уровне, значит уровень бесполезен, хотя в правило входит.
    ALLOWB = {"regular": 2, "silver": 3, "gold": 3}
    def bag_rule(v):
        tier = "gold" if v["tier_gold"] else ("silver" if v["tier_silver"] else "regular")
        return 50 * max(0, 2 - ALLOWB[tier])
    def bag_adm(v):
        return not (v["tier_gold"] and v["tier_silver"])   # уровень один
    ctl3 = sensitivity(["tier_gold", "tier_silver"], bag_rule, bag_adm)
    print(f"  3. числовое доминирование   : {ctl3}")
    if set(ctl3.values()) != {"SETTLES"}:
        fails.append("построенный числовой свидетель не опознан как SETTLES")

    # ОТРИЦАТЕЛЬНЫЕ КОНТРОЛИ — калибровка в ДРУГУЮ сторону. До них было
    # показано только, что прибор находит известный SETTLES. Требование
    # внешнего рецензента 2026-08-31: он обязан так же надёжно находить известный MOVES,
    # иначе чувствительность откалибрована лишь в одну сторону.
    print("\n  ОТРИЦАТЕЛЬНЫЕ КОНТРОЛИ (известный MOVES обязан находиться):")
    neg = [
        ("прямая зависимость f(p)=p", ["p"], lambda v: v["p"], None, "p", "MOVES"),
        ("p И q, q ЗАФИКСИРОВАНО истиной", ["p"],
         lambda v: v["p"] and True, None, "p", "MOVES"),
        ("p ИЛИ q, q ЗАФИКСИРОВАНО ложью", ["p"],
         lambda v: v["p"] or False, None, "p", "MOVES"),
        ("p ИЛИ q, q ЗАФИКСИРОВАНО истиной", ["p"],
         lambda v: v["p"] or True, None, "p", "SETTLES"),
    ]
    for name, preds, rule, adm, key, want in neg:
        got = sensitivity(preds, rule, adm)[key]
        mark = "ок" if got == want else "ПРОВАЛ"
        print(f"    {name:<38} -> {got:<8} (ждали {want}) {mark}")
        if got != want:
            fails.append(f"отрицательный контроль «{name}»: {got}, ждали {want}")
    print("    ПРИМЕЧАНИЕ: последний случай ФУНКЦИОНАЛЬНО инвариантен, но по")
    print("    старшинству разрядов это СОКРАЩЕНИЕ (наблюдённое q уже решило),")
    print("    а не settles. Старшинство применяет census_cancel, где известные")
    print("    факты есть; здесь правило голое и различить их нечем.")

    # ОГРАНИЧЕННАЯ ОБЛАСТЬ: недопустимые миры не голосуют
    ctl5 = sensitivity(["p", "q"], lambda v: v["p"] or v["q"],
                       admissible=lambda v: v["q"] != v["p"])
    print(f"\n  ограниченная область (q = НЕ p): {ctl5}")
    print("    при таком ограничении p ИЛИ q всегда истинно, значит оба SETTLES")
    if set(ctl5.values()) != {"SETTLES"}:
        fails.append("недопустимые миры всё ещё голосуют")

    if fails:
        print("\n  КОНТРОЛЬ ПРОВАЛЕН — перепись НЕДЕЙСТВИТЕЛЬНА:")
        for f in fails:
            print("   -", f)
        return 1
    print("  все три пройдены: прибор находит и отсутствие влияния, и")
    print("  избыточность, и доминирование.")
    print("\nПОТОЛОК: это ЛОГИЧЕСКАЯ чувствительность. Действенная экономия")
    print("не измерена: один вызов открывает несколько полей сразу.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
