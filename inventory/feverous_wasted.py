# -*- coding: utf-8 -*-
"""Куда на самом деле уходит время проверки — по следам разметчиков.

ОТДЕЛЬНЫЙ КАНАЛ, ДРУГАЯ ПРИВЯЗКА. Потолок из feverous_headroom.py считает
экономию от ИЗБЫТОЧНОСТИ: не покупать то, что перекрыто другим набором.
Здесь считается другое — сколько посещённых страниц НЕ дали ни одного
элемента итогового свидетельства, и сколько времени на них ушло.

ЧЕСТНАЯ ПРИВЯЗКА, И ЭТО ГЛАВНОЕ. Это блуждание ЧЕЛОВЕКА, который ответа не
знал и свидетельство ИСКАЛ. Наше преимущество — выбор между УЖЕ НАЗВАННЫМИ
проверками, а не поиск вслепую. Поэтому записывать эту величину в заслугу
ZTL нельзя; она говорит, где лежит время проверки, а не кто его сэкономит.
Приписать её себе было бы ровно тем подлогом, от которого метод предостерегает.
"""
import json, sys, statistics
from collections import Counter

FILES = sys.argv[1:] or ["feverous_data/feverous_dev_challenges.jsonl"]


def page_of(elem_id):
    """'Algebraic logic_sentence_0' -> 'Algebraic logic'."""
    for sep in ("_sentence_", "_cell_", "_header_cell_",
                "_table_caption_", "_item_"):
        if sep in elem_id:
            return elem_id.split(sep)[0]
    return elem_id


def main():
    n = 0
    visited_tot = fruitful_tot = 0
    waste_share = []
    time_tot = time_wasted = 0.0
    ops_kind = Counter()
    dropped = [0]

    for path in FILES:
        for line in open(path, encoding="utf-8"):
            try:
                rec = json.loads(line)
            except Exception:
                continue
            if (rec.get("label") or "").strip() not in ("SUPPORTS", "REFUTES"):
                continue
            ev = rec.get("evidence") or []
            elems = [e for s in ev for e in (s.get("content") or [])]
            if not elems:
                continue
            ops = rec.get("annotator_operations") or []
            if not ops:
                continue
            # ОТМЕТКИ ВРЕМЕНИ БЫВАЮТ АБСОЛЮТНЫЕ. Промерено 2026-08-31: у 83
            # записей dev последняя отметка — Unix-время (≈1.62e9), а не
            # секунды от начала разметки. Медиана по всем — 123 с, максимум
            # 1620961678. Одна такая запись даёт 51 тысячу часов и делает
            # сумму бессмысленной. Отбрасываем и СЧИТАЕМ отброшенные.
            try:
                span = float(ops[-1].get("time"))
            except Exception:
                span = None
            if span is None or span > 86400:
                dropped[0] += 1
                continue
            n += 1
            useful_pages = {page_of(e) for e in elems}

            # проходим след: 'Now on' задаёт текущую страницу, время идёт
            # до следующей операции
            cur, cur_t = None, None
            visited, fruitful = set(), set()
            for op in ops:
                kind = (op.get("operation") or "").strip()
                ops_kind[kind] += 1
                try:
                    t = float(op.get("time"))
                except Exception:
                    t = None
                if cur is not None and t is not None and cur_t is not None:
                    dt = max(0.0, t - cur_t)
                    time_tot += dt
                    if cur not in useful_pages:
                        time_wasted += dt
                if kind == "Now on":
                    cur = (op.get("value") or "").strip()
                    cur_t = t
                    if cur and not cur.startswith("?search="):
                        visited.add(cur)
                        if cur in useful_pages:
                            fruitful.add(cur)
                elif t is not None:
                    cur_t = t
            visited_tot += len(visited)
            fruitful_tot += len(fruitful)
            if visited:
                waste_share.append(1 - len(fruitful) / len(visited))

    print("=" * 66)
    print("КУДА УХОДИТ ВРЕМЯ ПРОВЕРКИ — следы разметчиков")
    print("=" * 66)
    print(f"\nКОНТРОЛЬ: разобрано записей со следами: {n}")
    print(f"  отброшено с абсолютной меткой времени: {dropped[0]}")
    if not n:
        print("НОЛЬ — отказ разбора, а не свойство данных.")
        return 2
    print(f"\nСТРАНИЦЫ")
    print(f"  посещено всего            : {visited_tot}")
    print(f"  дали итоговое свидетельство: {fruitful_tot}")
    print(f"  НЕ дали ничего            : {visited_tot - fruitful_tot}"
          f" = {(visited_tot-fruitful_tot)/visited_tot*100:.1f}%")
    print(f"  медиана доли пустых на запись: "
          f"{statistics.median(waste_share)*100:.1f}%")
    print(f"\nВРЕМЯ")
    print(f"  всего по следам, часов          : {time_tot/3600:.1f}")
    print(f"  на страницах без свидетельства  : {time_wasted/3600:.1f}"
          f" = {time_wasted/time_tot*100:.1f}%")
    print(f"\nОПЕРАЦИИ")
    for k, v in ops_kind.most_common(7):
        print(f"  {k:<18} {v:>8}")
    print("\nПРИВЯЗКА: это блуждание человека, ИСКАВШЕГО свидетельство.")
    print("Наше преимущество — выбор между уже названными проверками.")
    print("В заслугу ZTL эта величина НЕ ЗАПИСЫВАЕТСЯ.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
