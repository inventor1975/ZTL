# -*- coding: utf-8 -*-
"""AIRLINE-PILOT-001: перепись проверок в ПРАВИЛЕ ОТМЕНЫ, по настоящей базе.

Правило из wiki_airline.md (sha256 56c33580…, строки 54-60):

    cancel_allowed = no_segment_flown AND (
        within_24h OR airline_cancelled OR cabin=business
        OR (cabin IN {basic_economy, economy} AND insurance AND reason_covered))

ЧЕТЫРЕ ПРОВЕРКИ, которые агент обязан установить: within_24h, airline_cancelled,
cabin, insurance. (reason_covered сообщает пользователь, это не чтение базы.)

КАК КЛАССИФИЦИРУЕМ каждую проверку для конкретной брони:
  STATIC        — источник САМ объявил её неуместной. Здесь: уровень членства
                  («The rules are strict regardless of the membership status»).
  SHORT-CIRCUIT — при УЖЕ ИЗВЕСТНЫХ значениях прочих проверок исход этой
                  не меняет вердикта, и это видно порядком обхода.
  SETTLES       — оба исхода этой проверки живы, прочие НЕ определены, и
                  вердикт всё равно один. Считается перебором: фиксируем
                  проверку в T и в F, по остальным перебираем ВСЕ комбинации;
                  если множество вердиктов совпало — проверка бесполезна.
  JOINTNESS     — поодиночке не двигает, но в наборе двигает.

ПОТОЛОК: считается ОДНО правило политики. Не выдаётся за потолок задачи.
"""
import ast, itertools, json, os, sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
CHECKS = ["not_already_flown", "within_24h", "airline_cancelled",
          "cabin_business", "insurance", "covered_reason"]

# ДОПУСТИМОСТЬ КОМБИНАЦИЙ — иначе невозможный мир делает проверку «двигающей».
# Промерено по базе 2026-08-31:
#   все 6 пар cabin x insurance наблюдаются (336/313/334/341/325/351) —
#   значит эти две свободны, и перебор их законен ПО ДАННЫМ.
#   статусы рейсов: landed 3982, cancelled 373, available 4500, delayed 41,
#   flying 47, on time 57 — все нужные состояния достижимы.
# ОГРАНИЧЕНИЕ, найденное в источнике: рейс, отменённый ПЕРЕВОЗЧИКОМ, не мог
# быть пролетён. Значит airline_cancelled -> not_already_flown, и миры, где
# оба «да» вместе с already_flown, из перебора исключаются.


def admissible(v):
    if v["airline_cancelled"] and not v["not_already_flown"]:
        return False
    return True


def allowed(v):
    """ПОЛНОЕ правило отмены, дословно по источнику.

    ИСПРАВЛЕНО 2026-08-31 после разбора внешнего рецензента. Версия 1 (сохранена как
    УБИТЫЙ-ПУТЬ-002) выбрасывала `covered_reason` из формулы, хотя мой же
    докстринг его записывал, и оправдывала это тем, что его сообщает
    пользователь. К УСЛОВИЮ ДОПУСКА это отношения не имеет: страховка без
    покрытой причины отмену не разрешает. Это ровно шов «источник → формула»,
    случившийся в собственном приборе.

    Версия 1 также не перебирала not_already_flown вовсе — он стоял
    параметром со значением по умолчанию.
    """
    return v["not_already_flown"] and (
        v["within_24h"] or v["airline_cancelled"] or v["cabin_business"]
        or (v["insurance"] and v["covered_reason"]))


def classify(check, known):
    """ИСПРАВЛЕНО 2026-08-31 вместе с census_rest: SETTLES = при КАЖДОМ
    допустимом наборе прочих смена предиката не меняет последствия.

    Прежнее определение требовало ещё и глобальной постоянности вердикта и
    потому не находило булеву избыточность. Ошибка смещала к MOVES, то есть
    к NO-GO.
    """
    free = [c for c in CHECKS if c != check and c not in known]
    for combo in itertools.product([True, False], repeat=len(free)):
        base = dict(known); base.update(dict(zip(free, combo)))
        vt = dict(base); vt[check] = True
        vf = dict(base); vf[check] = False
        if not (admissible(vt) and admissible(vf)):
            continue
        if allowed(vt) != allowed(vf):
            return "MOVES"
    return "SETTLES"


def main():
    users = json.load(open(os.path.join(HERE, "db_users.json")))
    res = json.load(open(os.path.join(HERE, "db_reservations.json")))
    print("=" * 66)
    print("AIRLINE-PILOT-001 — перепись проверок ПРАВИЛА ОТМЕНЫ")
    print("=" * 66)
    print(f"\nКОНТРОЛЬ: броней в базе {len(res)}, пользователей {len(users)}")
    if len(res) != 2000:
        print("не 2000 броней — база не та, дальше не считаем")
        return 2

    # ЗАДАЧИ с отменой
    tree = ast.parse(open(os.path.join(HERE, "tasks_airline.py"), encoding="utf-8").read())
    tasks = next(n.value.elts for n in ast.walk(tree)
                 if isinstance(n, ast.Assign) and getattr(n.targets[0], "id", "") == "TASKS")
    cancel_tasks = []
    for i, t in enumerate(tasks):
        for node in ast.walk(t):
            if (isinstance(node, ast.Call) and getattr(node.func, "id", "") == "Action"):
                nm = rid = None
                for kw in node.keywords:
                    if kw.arg == "name":
                        nm = ast.literal_eval(kw.value)
                    if kw.arg == "kwargs":
                        try:
                            rid = ast.literal_eval(kw.value).get("reservation_id")
                        except Exception:
                            pass
                if nm == "cancel_reservation" and rid:
                    cancel_tasks.append((i, rid))
    print(f"  задач с отменой и известной бронью: {len(cancel_tasks)}")
    if not cancel_tasks:
        print("НОЛЬ — отказ разбора, не свойство данных.")
        return 2

    buckets = Counter()
    rows = []
    for ti, rid in cancel_tasks:
        r = res.get(rid)
        if not r:
            buckets["брони нет в базе"] += 1
            continue
        biz = r.get("cabin") == "business"
        ins = r.get("insurance") == "yes"
        # STATIC объявлен источником — считаем отдельной строкой, один раз на бронь
        buckets["STATIC (уровень членства, объявлено источником)"] += 1
        for c in CHECKS:
            k = classify(c, known={})
            buckets[f"{c}: {k}"] += 1
            rows.append((ti, rid, c, k, biz, ins))

    print("\nПО КАЖДОЙ ПРОВЕРКЕ, при НЕ определённых прочих:")
    for c in CHECKS:
        line = {k.split(": ")[1]: v for k, v in buckets.items() if k.startswith(c + ":")}
        print(f"  {c:<18} {line}")
    print(f"\n  {'STATIC (уровень членства)':<40} "
          f"{buckets['STATIC (уровень членства, объявлено источником)']}")

    tot = sum(v for k, v in buckets.items() if ":" in k and not k.startswith("STATIC"))
    settles = sum(v for k, v in buckets.items() if k.endswith(": SETTLES"))
    print(f"\nИТОГ по правилу отмены: проверок разобрано {tot}, "
          f"из них SETTLES {settles}")
    print("\nПОТОЛОК: одно правило политики, не потолок задачи.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
