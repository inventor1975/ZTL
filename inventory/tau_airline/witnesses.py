# -*- coding: utf-8 -*-
"""Свидетели MOVES с учётом СОСТОЯНИЯ ЗАДАЧИ + проход по действиям.

Требование внешнего рецензента 2026-08-31: строка MOVES держится, только если предъявлена
ПАРА допустимых состояний, различающихся ровно этим предикатом и дающих РАЗНОЕ
полное последствие, причём совместимых с тем, что задача уже зафиксировала.
Структура без такого свидетеля идёт как ТОЛЬКО ФОРМАЛЬНАЯ МОДЕЛЬ и NO-GO не
подпирает.

Второе: ПРОХОД ПО ПРИОБРЕТЕНИЯМ. Предикатный ноль не влечёт действенного нуля,
потому что один вызов открывает несколько полей разом. Для каждой РЕАЛЬНОЙ
операции спрашиваем: можно ли опустить её ЦЕЛИКОМ, не изменив последствия?
"""
import ast, itertools, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
CHECKS = ["not_already_flown", "within_24h", "airline_cancelled",
          "cabin_business", "insurance", "covered_reason"]


def allowed(v):
    return v["not_already_flown"] and (
        v["within_24h"] or v["airline_cancelled"] or v["cabin_business"]
        or (v["insurance"] and v["covered_reason"]))


def admissible(v):
    return not (v["airline_cancelled"] and not v["not_already_flown"])


def main():
    res = json.load(open(os.path.join(HERE, "db_reservations.json")))
    tree = ast.parse(open(os.path.join(HERE, "tasks_airline.py"), encoding="utf-8").read())
    tasks = next(n.value.elts for n in ast.walk(tree)
                 if isinstance(n, ast.Assign) and getattr(n.targets[0], "id", "") == "TASKS")
    cancels = []
    for i, t in enumerate(tasks):
        for node in ast.walk(t):
            if isinstance(node, ast.Call) and getattr(node.func, "id", "") == "Action":
                nm = rid = None
                for kw in node.keywords:
                    if kw.arg == "name":
                        nm = ast.literal_eval(kw.value)
                    if kw.arg == "kwargs":
                        try: rid = ast.literal_eval(kw.value).get("reservation_id")
                        except Exception: pass
                if nm == "cancel_reservation" and rid and rid in res:
                    cancels.append((i, rid, res[rid]))

    print("=" * 68)
    print("СВИДЕТЕЛИ MOVES С УЧЁТОМ СОСТОЯНИЯ ЗАДАЧИ")
    print("=" * 68)
    print(f"\nКОНТРОЛЬ: броней отмены с записью в базе {len(cancels)}")
    if not cancels:
        print("НОЛЬ — отказ разбора."); return 2

    # ИСПРАВЛЕНО НА ХОДУ 2026-08-31. Сперва я счёл класс и страховку
    # «зафиксированными состоянием задачи», потому что они лежат в записи
    # брони. Это неверно: до ЧТЕНИЯ брони агенту о них не известно ничего, и
    # именно их дознание и выясняет. Держать предикат фиксированным и при этом
    # искать ему свидетеля — противоречие.
    #
    # Запись брони служит другому: она подтверждает, что мир РЕАЛИЗУЕМ.
    # Свидетель = пара допустимых пополнений, различающихся ровно предикатом,
    # прочие значения которых встречаются у реальной брони.
    #
    # Смещение прежней версии шло ПРОТИВ моего же прежнего вывода (два
    # предиката уходили в «только формальную модель» и ослабляли NO-GO).
    # Направление роли не играет: неверно есть неверно.
    # Остальные три (окно 24 ч, отмена перевозчиком, налёт) в самой брони не
    # записаны и остаются свободными — это НАЗВАНО, а не скрыто.
    print("\nПРАВИЛО СВИДЕТЕЛЯ: предикат варьируется; прочие обязаны совпадать")
    print("с РЕАЛЬНОЙ бронью там, где она их задаёт (класс, страховка), и")
    print("свободны там, где в записи брони их нет.")

    found = {c: None for c in CHECKS}
    for ti, rid, r in cancels:
        # значения, РЕАЛИЗОВАННЫЕ этой бронью — для подтверждения реализуемости
        real = {"cabin_business": r.get("cabin") == "business",
                "insurance": r.get("insurance") == "yes"}
        for c in CHECKS:
            if found[c]:
                continue
            free = [q for q in CHECKS if q != c]
            for combo in itertools.product([True, False], repeat=len(free)):
                base = dict(zip(free, combo))
                # прочие ДОЛЖНЫ совпадать с реальной бронью там, где бронь их
                # задаёт: иначе свидетель опирался бы на выдуманный мир
                if any(q in real and base[q] != real[q] for q in free):
                    continue
                vt = dict(base); vt[c] = True
                vf = dict(base); vf[c] = False
                if not (admissible(vt) and admissible(vf)):
                    continue
                if allowed(vt) != allowed(vf):
                    found[c] = (ti, rid, {k: base[k] for k in sorted(base)})
                    break

    print("\nСВИДЕТЕЛИ (пара состояний, различающихся ровно этим предикатом):")
    formal_only = []
    for c in CHECKS:
        w = found[c]
        if w:
            ti, rid, ctx = w
            print(f"  {c:<18} ЕСТЬ — задача {ti}, бронь {rid}")
            print(f"                     прочие: {ctx}")
        else:
            print(f"  {c:<18} НЕТ СВИДЕТЕЛЯ -> ТОЛЬКО ФОРМАЛЬНАЯ МОДЕЛЬ")
            formal_only.append(c)

    print("\n" + "=" * 68)
    print("ПРОХОД ПО ПРИОБРЕТЕНИЯМ: можно ли ОПУСТИТЬ операцию целиком?")
    print("=" * 68)
    bundles = {
        "get_reservation_details": ["cabin_business", "insurance",
                                    "not_already_flown"],
        "get_user_details":        [],   # уровень членства — STATIC по источнику
        "вопрос пользователю о причине": ["covered_reason"],
        "статус рейса (поиск/детали)":   ["airline_cancelled"],
    }
    for op, fields in bundles.items():
        if not fields:
            print(f"  {op:<32} открывает только STATIC-поля -> "
                  f"МОЖНО ОПУСТИТЬ для правила отмены")
            continue
        # можно опустить, если ПРИ ЛЮБОМ совместном исходе набора последствие одно
        free = [q for q in CHECKS if q not in fields]
        outs = set()
        for own in itertools.product([True, False], repeat=len(fields)):
            for combo in itertools.product([True, False], repeat=len(free)):
                v = dict(zip(fields, own)); v.update(dict(zip(free, combo)))
                if not admissible(v):
                    continue
                outs.add(allowed(v))
        can_omit = len(outs) == 1
        print(f"  {op:<32} поля {fields} -> "
              f"{'МОЖНО ОПУСТИТЬ' if can_omit else 'НЕЛЬЗЯ ОПУСТИТЬ'}")

    print("\nИТОГ")
    print(f"  предикатов со свидетелем задачи : {len(CHECKS)-len(formal_only)} из {len(CHECKS)}")
    print(f"  только формальная модель        : {formal_only or 'нет'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
