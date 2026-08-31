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


def consequence(tier_idx, cabin, bags):
    """ПОЛНОЕ последствие багажного правила: доплата в долларах."""
    return 50 * max(0, bags - ALLOW[cabin][tier_idx])


def generic_baseline_eliminates(cabin, bags):
    """ОБЫЧНЫЙ вычислитель с конечной областью — без всякого ZTL.

    Перебирает три значения уровня, считает полное последствие для каждого и
    объявляет проверку ненужной, если все совпали. Три строки. Именно этот
    базис внешний рецензент и требует вычесть, прежде чем что-то записывать нам.
    """
    outs = {consequence(i, cabin, bags) for i in range(3)}
    return len(outs) == 1


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
    settles, matters, short_circuit = [], [], []
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
                # СОКРАЩЕНИЕ, а не «вырожденный settles». Поправка внешнего рецензента
                # 2026-08-31: я завёл ПЯТУЮ корзину, чтобы сохранить первую
                # классификацию. Решать надо по структуре решения.
                #
                # доплата = 50 * max(0, bags - allowance(уровень, класс))
                # При bags = 0 внешний max обращается в ноль ПРИ ЛЮБОМ
                # allowance. То есть НАБЛЮДЁННОЕ значение (запрошено ноль)
                # уже определяет полное последствие, и уровень мёртв по той
                # же причине, по какой мёртв правый операнд у `&&`.
                # Это ровно определение СОКРАЩЕНИЯ в замороженном разбиении.
                short_circuit.append(rec)
            elif bags <= mn:
                settles.append(rec)
            else:
                matters.append(rec)
        kinds["с багажом" if touched else "без багажа"] += 1

    print(f"  задач С багажным действием : {kinds['с багажом']}")
    print(f"  задач БЕЗ багажа           : {kinds['без багажа']}")
    if kinds.get("класс или число мест не назван"):
        print(f"  не хватило полей           : {kinds['класс или число мест не назван']}")

    tot = len(settles) + len(matters) + len(short_circuit)
    if not tot:
        print("\nНОЛЬ пригодных багажных действий — отказ разбора, не свойство данных.")
        return 2

    nd = len(settles) + len(matters)
    print(f"\nБАГАЖНЫХ ДЕЙСТВИЙ С КЛАССОМ И ЧИСЛОМ МЕСТ: {tot}")
    print(f"  СОКРАЩЕНИЕ (запрошено 0 мест)    : {len(short_circuit)}"
          f" — наблюдение уже решило, заявлять нечего")
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

    # ТРИ ЧИСЛА, а не одно — требование внешнего рецензента 2026-08-31
    print("\nВЫЧИТАЕМ ОБЫЧНЫЙ ВЫЧИСЛИТЕЛЬ (перебор области уровня):")
    gen_short = sum(1 for _, c, b, _, _ in short_circuit
                    if generic_baseline_eliminates(c, b))
    gen_set = sum(1 for _, c, b, _, _ in settles
                  if generic_baseline_eliminates(c, b))
    residual = len(settles) - gen_set
    print(f"  наших settles (невырожденных)        : {len(settles)}")
    print(f"  из них берёт ОБЫЧНЫЙ вычислитель     : {gen_set}")
    print(f"  ОСТАТОК, уникально наш               : {residual}")
    print(f"  (для сведения: сокращений, которые он тоже берёт: "
          f"{gen_short} из {len(short_circuit)})")
    if residual == 0 and len(settles) == 0:
        print("\n  ОСТАТОК НОЛЬ ПРИ НУЛЕ НАХОДОК — это НЕ «мы не хуже».")
        print("  Находок нет вовсе, значит вычитать не из чего, и утверждать")
        print("  об остатке на этих данных НЕЛЬЗЯ ни в ту, ни в другую сторону.")

    print("\nПОТОЛОК: посчитана ОДНА проверка — уровень членства в багажном")
    print("правиле. Это НЕ потолок задачи и не выдаётся за него.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
