# -*- coding: utf-8 -*-
"""HEADROOM-PRECHECK-001 — сколько места для экономии есть в САМОМ FEVEROUS.

Процедура заморожена в HEADROOM-PRECHECK-001_МЕТОД.md, прогноз чисел —
в feverous_precheck_ПРОГНОЗ.md. Оба написаны ДО скачивания.

Ни одного вызова модели. Считаем по разметке датасета и только по ней.

КОНТРОЛЬ ВСТРОЕН: печатаем, сколько строк прочитано и сколько отброшено.
Разбор входа умеет давать ЛОЖНЫЙ НОЛЬ — молча пропустить всё и отчитаться
нулём. Поэтому число отброшенных всегда на экране, а не в уме.
"""
import json, sys, statistics
from collections import Counter

FILES = sys.argv[1:] or ["feverous_data/feverous_dev_challenges.jsonl"]


def sets_of(rec):
    """Наборы свидетельств как множества идентификаторов элементов."""
    out = []
    for s in rec.get("evidence") or []:
        c = s.get("content") if isinstance(s, dict) else None
        if c:
            out.append(frozenset(c))
    return out


def non_nested(sets):
    """Оставить только те наборы, что не вложены в другой.

    Вложенный набор НЕ даёт альтернативы: если A подмножество B, покупка
    ради B закрывает и A. Альтернатива есть, только когда ни один набор не
    поглощает другой."""
    keep = []
    for i, a in enumerate(sets):
        if any(i != j and a >= b for j, b in enumerate(sets)):
            # a поглощает b — a не «альтернатива», а надмножество
            pass
        if not any(i != j and a < b for j, b in enumerate(sets)):
            keep.append(a)
    # уникальные
    return list(dict.fromkeys(keep))


def main():
    total_lines = skipped = 0
    labels = Counter()
    challenges = Counter()
    n_sets_dist = Counter()
    min_size_dist = Counter()
    redundant = 0          # ≥2 невложенных набора
    eligible = 0           # SUPPORTS / REFUTES с непустой разметкой
    sum_union = sum_min = 0
    red_sum_union = red_sum_min = 0
    joint = 0              # минимальный набор из ≥2 элементов
    have_ops = 0
    op_times = []

    for path in FILES:
        for line in open(path, encoding="utf-8"):
            total_lines += 1
            try:
                rec = json.loads(line)
            except Exception:
                skipped += 1
                continue
            lab = (rec.get("label") or "").strip()
            if not lab:
                skipped += 1
                continue
            labels[lab] += 1
            ch = (rec.get("challenge") or "").strip()
            if ch:
                challenges[ch] += 1
            if lab not in ("SUPPORTS", "REFUTES"):
                continue
            ss = sets_of(rec)
            if not ss:
                skipped += 1
                continue
            eligible += 1
            nn = non_nested(ss)
            n_sets_dist[len(nn)] += 1
            union = set().union(*ss)
            mn = min(len(s) for s in nn)
            min_size_dist[mn] += 1
            sum_union += len(union)
            sum_min += mn
            if mn >= 2:
                joint += 1
            if len(nn) >= 2:
                redundant += 1
                red_sum_union += len(union)
                red_sum_min += mn
            ops = rec.get("annotator_operations") or []
            if ops:
                have_ops += 1
                try:
                    t = float(ops[-1].get("time"))
                    if t > 0:
                        op_times.append(t)
                except Exception:
                    pass

    print("=" * 66)
    print("HEADROOM-PRECHECK-001 — счёт по разметке FEVEROUS")
    print("=" * 66)
    print(f"\nКОНТРОЛЬ РАЗБОРА")
    print(f"  строк прочитано            : {total_lines}")
    print(f"  отброшено (пусто/без меток): {skipped}")
    print(f"  пригодных (SUPPORTS/REFUTES с разметкой): {eligible}")
    if eligible == 0:
        print("\nНОЛЬ ПРИГОДНЫХ — это отказ разбора, а не свойство данных.")
        return 2

    nei = labels.get("NOT ENOUGH INFO", 0)
    tot_lab = sum(labels.values())
    print(f"\nN3 — НЕЧЕГО РЕШАТЬ")
    print(f"  NOT ENOUGH INFO: {nei} из {tot_lab} = {nei/tot_lab*100:.1f}%")

    print(f"\nN2 — ШИРИНА (размер самого дешёвого достаточного набора)")
    for k in sorted(min_size_dist)[:6]:
        print(f"  {k:>2} элемент(ов): {min_size_dist[k]:>6}"
              f"  ({min_size_dist[k]/eligible*100:5.1f}%)")
    big = sum(v for k, v in min_size_dist.items() if k >= 7)
    if big:
        print(f"  7 и больше    : {big:>6}  ({big/eligible*100:5.1f}%)")
    print(f"  ИТОГО ≥2 элементов (совместность): "
          f"{joint} = {joint/eligible*100:.1f}%")

    print(f"\nN1 — ИЗБЫТОЧНОСТЬ (≥2 невложенных набора)")
    for k in sorted(n_sets_dist):
        print(f"  {k} набор(ов): {n_sets_dist[k]:>6}"
              f"  ({n_sets_dist[k]/eligible*100:5.1f}%)")
    print(f"  ИТОГО с альтернативой: {redundant} = "
          f"{redundant/eligible*100:.1f}%")

    print(f"\nВ2 — ПОТОЛОК СОКРАЩЕНИЯ В ДЕЙСТВИЯХ (ВЕРХНЯЯ оценка)")
    print(f"  элементов в объединении всех наборов: {sum_union}")
    print(f"  элементов в дешёвом достаточном     : {sum_min}")
    ceil_all = (sum_union - sum_min) / sum_union * 100
    print(f"  потолок по ВСЕМ пригодным           : {ceil_all:.1f}%")
    if redundant:
        ceil_red = (red_sum_union - red_sum_min) / red_sum_union * 100
        print(f"  потолок ВНУТРИ избыточных случаев   : {ceil_red:.1f}%")

    print(f"\nСЛЕДЫ РАЗМЕТЧИКОВ")
    print(f"  записей со следами: {have_ops} из {eligible} "
          f"({have_ops/eligible*100:.1f}%)")
    if op_times:
        print(f"  медиана времени разметки: "
              f"{statistics.median(op_times):.0f} с "
              f"(n={len(op_times)})")

    print(f"\nТИПЫ ТРУДНОСТИ (разметка датасета)")
    for ch, n in challenges.most_common(8):
        print(f"  {ch:<30} {n:>6}  ({n/tot_lab*100:5.1f}%)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
