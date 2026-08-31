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
CHECKS = ["within_24h", "airline_cancelled", "cabin_business", "insurance"]


def allowed(v, no_flown=True):
    """Полное правило отмены при значениях проверок v (кроме no_segment_flown)."""
    if not no_flown:
        return False
    return (v["within_24h"] or v["airline_cancelled"] or v["cabin_business"]
            or ((not v["cabin_business"]) and v["insurance"]))


def classify(check, known):
    """Меняет ли исход `check` вердикт, когда прочие НЕ определены.

    known: словарь уже установленных проверок (для сокращения).
    Возвращает 'SHORT-CIRCUIT' | 'SETTLES' | 'MOVES'.
    """
    free = [c for c in CHECKS if c != check and c not in known]
    verdicts = set()
    per_branch = {}
    for val in (True, False):
        vs = set()
        for combo in itertools.product([True, False], repeat=len(free)):
            v = dict(known); v[check] = val
            v.update(dict(zip(free, combo)))
            vs.add(allowed(v))
        per_branch[val] = vs
        verdicts |= vs
    # если при ИЗВЕСТНЫХ прочих вердикт уже один — это сокращение
    if known and len(verdicts) == 1:
        return "SHORT-CIRCUIT"
    # оба исхода дают одно и то же множество вердиктов, и оно одноэлементно
    if per_branch[True] == per_branch[False] and len(verdicts) == 1:
        return "SETTLES"
    return "MOVES"


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
