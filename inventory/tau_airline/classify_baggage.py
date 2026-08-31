# -*- coding: utf-8 -*-
"""AIRLINE-PILOT-001: считаем, где проверка УРОВНЯ ЧЛЕНСТВА ничего не решает.

Замороженный прогноз (2026-08-31, до данных) говорил: настоящий `settles`
сядет в числовых нормах. Багажная норма — единственное место в политике,
где он возможен без сокращения. Здесь мы это СЧИТАЕМ, а не рассуждаем.

НОРМА ИЗ ИСТОЧНИКА (wiki_airline.md, sha256 56c33580…, строка 36):
                basic_economy  economy  business
    regular          0            1         2
    silver           1            2         3
    gold             2            3         3
    лишнее место — 50 долларов

РАЗБОР: проверка уровня БЕСПОЛЕЗНА ровно когда запрошено мест не больше
минимума по уровням для этого класса: тогда и допуск, и ЦЕНА (ноль долларов)
одинаковы при всех трёх значениях. Это НЕ сокращение — ни одно наблюдённое
значение исхода не определяет, решает минимум по области неизвестного.

ПОТОЛОК: считается ОДНА проверка из многих — уровень членства в багажном
правиле. Это не потолок задачи целиком и не выдаётся за него.
"""
import ast, os, sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
ALLOW = {  # класс -> (regular, silver, gold)
    "basic_economy": (0, 1, 2),
    "economy": (1, 2, 3),
    "business": (2, 3, 3),
}


def tasks_from(path):
    """Разбираем ИСХОДНИК дерева, а не импортируем чужой пакет."""
    tree = ast.parse(open(path, encoding="utf-8").read())
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign) and getattr(node.targets[0], "id", "") == "TASKS":
            return node.value.elts
    return []


def kwargs_of(call):
    for kw in call.keywords:
        if kw.arg == "kwargs":
            try:
                return ast.literal_eval(kw.value)
            except Exception:
                return {}
    return {}


def main():
    path = os.path.join(HERE, "tasks_airline.py")
    elts = tasks_from(path)
    print("=" * 66)
    print("AIRLINE-PILOT-001 — проверка УРОВНЯ в багажном правиле")
    print("=" * 66)
    print(f"\nКОНТРОЛЬ РАЗБОРА: задач найдено {len(elts)}")
    if len(elts) != 50:
        print("НЕ 50 — разбор не тот, дальше не считаем.")
        return 2

    kinds = Counter()
    settles, matters, degenerate = [], [], []
    for i, t in enumerate(elts):
        touched = False
        for node in ast.walk(t):
            if not (isinstance(node, ast.Call) and
                    getattr(node.func, "id", "") == "Action"):
                continue
            kw = kwargs_of(node)
            if "total_baggages" not in kw:
                continue
            touched = True
            cabin = kw.get("cabin")
            bags = kw.get("total_baggages")
            if cabin not in ALLOW or not isinstance(bags, int):
                kinds["класс или число мест не назван"] += 1
                continue
            mn = min(ALLOW[cabin])
            rec = (i, cabin, bags, mn, kw.get("nonfree_baggages"))
            if bags == 0:
                # ВЫРОЖДЕННЫЙ. Ноль мест не стоит ничего ни при каком уровне.
                # Формально это settles, но заслуги в нём нет: так ответит и
                # человек, и любой базовый агент. Считать его вместе с
                # настоящими — ровно то раздувание свидетельства, против
                # которого вся программа.
                degenerate.append(rec)
            elif bags <= mn:
                settles.append(rec)
            else:
                matters.append(rec)
        kinds["с багажом" if touched else "без багажа"] += 1

    print(f"  задач С багажным действием : {kinds['с багажом']}")
    print(f"  задач БЕЗ багажа           : {kinds['без багажа']}")
    if kinds.get("класс или число мест не назван"):
        print(f"  не хватило полей           : {kinds['класс или число мест не назван']}")

    tot = len(settles) + len(matters) + len(degenerate)
    if not tot:
        print("\nНОЛЬ пригодных багажных действий — отказ разбора, не свойство данных.")
        return 2

    nd = len(settles) + len(matters)
    print(f"\nБАГАЖНЫХ ДЕЙСТВИЙ С КЛАССОМ И ЧИСЛОМ МЕСТ: {tot}")
    print(f"  ВЫРОЖДЕННЫХ (запрошено 0 мест)   : {len(degenerate)}"
          f" — заслуги нет, считаем отдельно")
    print(f"  НЕВЫРОЖДЕННЫХ (мест >= 1)        : {nd}")
    if nd:
        print(f"    проверка уровня не решает (settles): "
              f"{len(settles)} = {len(settles)/nd*100:.0f}% от невырожденных")
        print(f"    проверка уровня РЕШАЕТ            : "
              f"{len(matters)} = {len(matters)/nd*100:.0f}% от невырожденных")
    else:
        print("    НЕВЫРОЖДЕННЫХ НЕТ — доля settles не определена, а не равна нулю")

    print("\n  где не решает (класс, мест, минимум по уровням):")
    for i, c, b, mn, nf in settles[:8]:
        print(f"    задача {i:>2}: {c:<13} мест {b}, минимум {mn}, nonfree={nf}")
    print("\n  где решает:")
    for i, c, b, mn, nf in matters[:8]:
        print(f"    задача {i:>2}: {c:<13} мест {b}, минимум {mn}, nonfree={nf}")

    print("\nПОТОЛОК: посчитана ОДНА проверка — уровень членства в багажном")
    print("правиле. Это НЕ потолок задачи и не выдаётся за него.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
