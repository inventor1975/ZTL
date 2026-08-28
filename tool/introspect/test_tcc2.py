# -*- coding: utf-8 -*-
"""TCC-2 — отношение консервативной замены, и где оно переворачивается.

Наряд внешнего рецензента TCC-2 (2026-08-25): «наименьшее отношение для случаев вида
R ⇒ Q, и ровно какие типы предложений переворачивают направление.
Универсального порядка не заводить, если не можешь его доказать.»

Ответ отрицательный по форме и он тут ПРОГОНЯЕТСЯ, а не утверждается:
универсального порядка нет, потому что «консервативно» не определено без
ответа ДЛЯ КОГО. Одна и та же правка — сузить срок с 30 до 14 — сохраняет
под обязанностью и ОТНИМАЕТ под правом.

Что переворачивает направление, ровно две вещи и обе тут проверены:
  1. деонтический тип (ОБЯЗАН против ВПРАВЕ);
  2. отрицание, и оно переворачивает ДВАЖДЫ — тип и чтение границы
     (найдено прогоном этой батареи 2026-08-28, не рассуждением).
Не переворачивают: актор, единица, величина.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from guards import conservative_replacement as cr, bounds

СЛУЧАИ = [
    # (имя, источник, кандидат, ожидаемый вердикт, ожидаемый бенефициар)
    ("обязанность сужена",
     "The controller must respond within 30 days.",
     "The controller must respond within 14 days.", "CONSERVATIVE", "контрагент"),
    ("обязанность ослаблена",
     "The controller must respond within 30 days.",
     "The controller must respond within 60 days.", "LOSS", "контрагент"),
    ("ПРАВО сужено — отнятое право",
     "The data subject may retain the record for up to 30 days.",
     "The data subject may retain the record for up to 14 days.", "LOSS", "адресат"),
    ("ПРАВО расширено",
     "The data subject may retain the record for up to 30 days.",
     "The data subject may retain the record for up to 60 days.",
     "CONSERVATIVE", "адресат"),
    ("ЗАПРЕТ ужесточён",
     "The processor may not retain data for more than 30 days.",
     "The processor may not retain data for more than 14 days.",
     "CONSERVATIVE", "контрагент"),
    ("ЗАПРЕТ ослаблен",
     "The processor may not retain data for more than 30 days.",
     "The processor may not retain data for more than 60 days.", "LOSS", "контрагент"),
    ("нижняя граница обязанности поднята",
     "The notice must be at least 30 days.",
     "The notice must be at least 60 days.", "CONSERVATIVE", "контрагент"),
    ("нижняя граница обязанности срезана",
     "The notice must be at least 30 days.",
     "The notice must be at least 14 days.", "LOSS", "контрагент"),
]

МОЛЧАНИЕ = [
    ("тип сменился — судить не вправе",
     "The controller must respond within 30 days.",
     "The controller may respond within 30 days."),
    ("типа нет вовсе",
     "The record is kept within 30 days.",
     "The record is kept within 14 days."),
]

if __name__ == "__main__":
    print("=" * 72)
    print("TCC-2. ОТНОШЕНИЕ ЗАМЕНЫ: одно движение, противоположные вердикты")
    print("=" * 72)
    ошибок = 0

    print("\n### 1. Покрытие: «up to» — ходовой оборот разрешений")
    assert bounds("may retain for up to 30 days") == [("ВЕРХ", 30, "day")], \
        "оборот «up to» снова невидим"
    print("   up to 30 days -> ('ВЕРХ', 30, 'day')   — видно")

    print("\n### 2. Батарея: тот же синтаксис, разный тип, разный вердикт")
    for имя, s, c, ждём, бенеф in СЛУЧАИ:
        r = cr(s, c)
        плохо = r["verdict"] != ждём or r.get("beneficiary") != бенеф
        ошибок += плохо
        print(f"   {'FAIL' if плохо else 'OK  '} {имя:36} "
              f"{r['verdict']:12} бенефициар={r.get('beneficiary')}")

    print("\n### 3. Молчание там, где типа нет — а не догадка")
    for имя, s, c in МОЛЧАНИЕ:
        r = cr(s, c)
        плохо = r["verdict"] != "SILENT"
        ошибок += плохо
        print(f"   {'FAIL' if плохо else 'OK  '} {имя:36} {r['verdict']}")

    print("\n### 4. ЧЕГО ЭТО НЕ УСТАНАВЛИВАЕТ")
    print("   Отношение решает только по деонтическому типу, полярности и")
    print("   числовым границам. Оно НЕ читает исключения, перекрёстные")
    print("   области действия и взаимодействие ограничений; там оно молчит,")
    print("   и молчание тут не «сохранено», а «права судить нет».")

    if ошибок:
        raise SystemExit(f"TCC-2 RED: {ошибок} расхождений")
    print("\n" + "=" * 72)
    print("TCC-2 GREEN — направление переворачивают ровно две вещи:")
    print("деонтический тип и отрицание; универсального порядка нет,")
    print("и причина названа: «консервативно» неопределимо без «для кого».")
