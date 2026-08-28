# -*- coding: utf-8 -*-
"""Путь наверх: подъём по ВЫПОЛНИМОСТИ, а не по согласию.

Отвечает на упрёк, найденный в чужой работе и признанный своим: «нет пути,
которым законная непроверенная информация могла бы КОГДА-ЛИБО подействовать».
Ворота, умеющие только отказывать, ещё не механизм управления.

Их ответ — социальный (двое независимых поручились). Наш — операционный:
основание входит само, если названный им АКТ существует и ПРОХОДИТ. Причина
отказа от их ответа промерена у нас же: `db/probe_containment.py` вводит
МНИМУЮ избыточность — два основания объявлены разными, происхождение одно.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault("ZTL_PY", sys.executable)
import ground_admission as ga

if __name__ == "__main__":
    print("=" * 72)
    print("ПУТЬ НАВЕРХ: по выполнимости, не по согласию")
    print("=" * 72)
    fails = 0

    def check(имя, ок):
        global fails
        fails += (not ок)
        print(f"   {'FAIL' if not ок else 'OK  '} {имя}")

    print("\n### 1. АКТ, который проходит, поднимает основание сам")
    r = ga.elevate("admission/test_tcc2.py", "act")
    check("зелёный прогон -> допущено", r["admissible"] and r["reason"] == "ACT_PASSED")

    print("\n### 2. Отказ НАЗЫВАЕТ причину, а не молчит")
    check("нет такого прогона",
          ga.elevate("нет-такого.py", "act")["reason"] == "NO_SUCH_ACT")
    check("ярус неизвестен",
          ga.elevate("x", "чепуха")["reason"] == "UNKNOWN_TIER")

    print("\n### 3. СТИПУЛЯЦИЯ не поднимается САМА — и это решение, не недоделка")
    r3 = ga.elevate("master", "story")
    check("story требует человека",
          not r3["admissible"] and r3["reason"] == "STIPULATION_NEEDS_A_PERSON")

    print("\n### 4. МЕСТО: открыть и посмотреть, а не поверить")
    check("документ есть и в нём искомое",
          ga.elevate("book/13-na-chem-vse-stoit.md", "place", "Агриппа")["reason"]
          == "PLACE_CONFIRMS")
    check("документ есть, искомого НЕТ — отказ",
          ga.elevate("book/13-na-chem-vse-stoit.md", "place",
                     "такого текста тут нет")["reason"] == "PLACE_SILENT")
    check("без искомого — допущено, но сказано, что не сверялось",
          ga.elevate("book/13-na-chem-vse-stoit.md", "place")["reason"]
          == "PLACE_EXISTS")

    print("\n### 5. ДВЕРЬ ВНУТРЬ ЗАКРЫТА — модуль ИСПОЛНЯЕТ КОД")
    # Найдено в своём же коде ДО выката: основание приходит из документа, и
    # «../../что-нибудь.py» заставил бы прибор выполнить чужой файл.
    for злой in ("../../../etc/passwd", "/etc/passwd",
                 "../ztl-private/guard-probe/measure_rules.py"):
        check(f"вне дерева отвергнуто: {злой[:34]}",
              ga.elevate(злой, "act")["reason"] == "ACT_OUTSIDE_TREE")

    print("\n### 6. ЧЕГО ЭТО НЕ УСТАНАВЛИВАЕТ")
    print("   Что акт ПРАВ — не устанавливается. Устанавливается, что акт")
    print("   СУЩЕСТВУЕТ и ПРОХОДИТ. Истинность добытого остаётся вопросом")
    print("   судьи. И реестр остаётся тем, что объявляет ХОЗЯИН прогона:")
    print("   кормить этот модуль основаниями из недоверенного документа")
    print("   нельзя, потому что он запускает код.")

    if fails:
        raise SystemExit(f"ADMISSION RED: {fails} расхождений")
    print("\n" + "=" * 72)
    print("GROUND ADMISSION GREEN — путь наверх есть для того, что можно")
    print("проверить действием, и его НЕТ для того, что держится на слове.")
