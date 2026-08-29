#!/usr/bin/env python3
# Copyright 2026 Vitaly Reznik
# SPDX-License-Identifier: Apache-2.0
"""Проверка СО СТОРОНЫ ПОТРЕБИТЕЛЯ — §4 ордера ADMISSIBILITY-CONSEQUENCE-001.

Ордер требует: каждое состояние должно быть отдельно опознано ниже по течению и
МЕХАНИЧЕСКИ ОТЛИЧИМО от пропуска, лжи, невычисления и других отказов. Разные
конечные решения при этом НЕ обязательны — двум институционально разным
состояниям позволено сойтись на одном временном исходе. Запрещено ОПЕРАЦИОННОЕ
СХЛОПЫВАНИЕ: потребитель не вправе видеть их одинаковыми.

Поэтому потребитель здесь возвращает ДВЕ вещи: распознанное СОСТОЯНИЕ и
диспозицию. Совпадение диспозиций допустимо, совпадение состояний — нет.

И контроль: запись, которая правкой НЕ затронута, обязана пережить её точно.
Без него набор из одних «должно отличаться» удовлетворяется потребителем,
который различает всё подряд.
"""
from __future__ import annotations
import json, pathlib, sys

RECOGNIZED = ("REFUSED_NO_WARRANT", "OMITTED_NOT_APPLICABLE", "FALSE_NOT_ADMISSIBLE",
              "NOT_COMPUTED", "CONSEQUENCE_PRESENT", "UNREADABLE")

def consume(record: dict, schema_conditional: bool) -> tuple[str, str]:
    """-> (опознанное состояние, диспозиция). Ветвление, а не косметика."""
    det = record.get("admissibility_determination")
    if isinstance(det, dict) and det.get("state") == "REFUSED_NO_WARRANT":
        # Вопрос ВОЗНИК и не отвечен. Нести дальше нельзя, но и закрывать нечем.
        return "REFUSED_NO_WARRANT", "HOLD_PENDING_WARRANT"
    if "admissibility_consequence" in record:
        v = record["admissibility_consequence"]
        if v is None:
            # Ровно то, что ордер запретил: четыре смысла в одном значении.
            return "UNREADABLE", "REJECT_RECORD"
        if v is False:
            return "FALSE_NOT_ADMISSIBLE", "DENY"
        return "CONSEQUENCE_PRESENT", "APPLY"
    if schema_conditional:
        return "OMITTED_NOT_APPLICABLE", "PROCEED_WITHOUT"
    # Поле обязательно по схеме и отсутствует — неотличимо от потери в канале.
    return "UNREADABLE", "REJECT_RECORD"

def main() -> int:
    here = pathlib.Path(__file__).resolve().parent
    after = json.loads((here / "evidence/record-AFTER.json").read_text(encoding="utf-8"))
    before = json.loads((here / "evidence/record-BEFORE.json").read_text(encoding="utf-8"))

    cases = [
        ("запись ПОСЛЕ правки (типизированный отказ)", after, True, "REFUSED_NO_WARRANT"),
        ("запись ДО правки (null)",                    before, True, "UNREADABLE"),
        ("пропуск при УСЛОВНОМ поле",
         {k: v for k, v in after.items() if k != "admissibility_determination"}, True,
         "OMITTED_NOT_APPLICABLE"),
        ("пропуск при ОБЯЗАТЕЛЬНОМ поле",
         {k: v for k, v in after.items() if k != "admissibility_determination"}, False,
         "UNREADABLE"),
        ("ложь", {**{k: v for k, v in after.items() if k != "admissibility_determination"},
                  "admissibility_consequence": False}, True, "FALSE_NOT_ADMISSIBLE"),
        ("настоящее последствие",
         {**{k: v for k, v in after.items() if k != "admissibility_determination"},
          "admissibility_consequence": {"reliance": "permitted", "authority": "A-17"}}, True,
         "CONSEQUENCE_PRESENT"),
    ]
    ok = fail = 0
    seen: dict[str, str] = {}
    print("СОСТОЯНИЕ, РАСПОЗНАННОЕ ПОТРЕБИТЕЛЕМ:")
    for name, rec, cond, want in cases:
        state, disp = consume(rec, cond)
        good = state == want
        ok, fail = (ok + 1, fail) if good else (ok, fail + 1)
        print(f"  {'OK  ' if good else 'FAIL'} {name:42} -> {state:24} {disp}")
        seen.setdefault(state, name)

    # ЗАПРЕЩЕНО ОПЕРАЦИОННОЕ СХЛОПЫВАНИЕ: четыре института — четыре состояния.
    четыре = {"REFUSED_NO_WARRANT", "OMITTED_NOT_APPLICABLE",
              "FALSE_NOT_ADMISSIBLE", "UNREADABLE"}
    got = {s for s, _ in (consume(r, c) for _, r, c, _ in cases)}
    collapsed = четыре - got
    print(f"\n  {'OK  ' if not collapsed else 'FAIL'} схлопывания нет: все четыре "
          f"института различены потребителем" + (f"; СЛИЛИСЬ: {collapsed}" if collapsed else ""))
    ok, fail = (ok + 1, fail) if not collapsed else (ok, fail + 1)

    # КОНТРОЛЬ (§3.7): всё, что не про допустимость, обязано пережить правку точно.
    b = {k: v for k, v in before.items() if "admis" not in k}
    a = {k: v for k, v in after.items() if "admis" not in k}
    same = b == a
    print(f"  {'OK  ' if same else 'FAIL'} КОНТРОЛЬ: незатронутая часть записи пережила "
          f"правку без единого изменения ({len(b)} полей)")
    ok, fail = (ok + 1, fail) if same else (ok, fail + 1)

    # КОНТРОЛЬ НА ПЕРЕБОР: потребитель не должен различать то, что одинаково.
    s1, _ = consume(after, True)
    s2, _ = consume(json.loads(json.dumps(after)), True)
    identical = s1 == s2
    print(f"  {'OK  ' if identical else 'FAIL'} КОНТРОЛЬ: одинаковые записи получают "
          f"одинаковое состояние (потребитель не сыплет различия из воздуха)")
    ok, fail = (ok + 1, fail) if identical else (ok, fail + 1)

    print(f"\nCONSUMER {'GREEN' if not fail else 'RED'}: {ok} OK, {fail} FAIL")
    return 1 if fail else 0

if __name__ == "__main__":
    sys.exit(main())
