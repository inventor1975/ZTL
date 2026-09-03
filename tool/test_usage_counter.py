#!/usr/bin/env python3
# Copyright 2026 Vitaly Reznik
# SPDX-License-Identifier: Apache-2.0
"""Счёт расхода: стенд БЕЗ СЕТИ, потому что стенд, требующий ключа, не гоняют.

Считается ФАКТ провайдера, а не наша оценка по длине текста. Отсюда и главное
свойство, которое здесь проверяется: **молчание провайдера не есть ноль**.
Вызов, где usage не пришёл, обязан попасть в `без_счёта`, а не раствориться —
иначе сумма выглядит полной, будучи неполной, и это ровно то ложное зелёное,
против которого весь проект.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import providers  # noqa: E402

ok = fail = 0


def check(имя, want, got):
    global ok, fail
    if want == got:
        ok += 1
        print(f"  [ок ] {имя}")
    else:
        fail += 1
        print(f"  [ПРОВАЛ] {имя}\n         ждали {want!r}, вышло {got!r}")


print("СЧЁТ РАСХОДА")
providers.usage_reset()
check("после сброса счёт пуст", {}, providers.usage_report())

providers._usage_add("groq", "m1", {"usage": {"prompt_tokens": 10,
                                              "completion_tokens": 4,
                                              "total_tokens": 14}})
r = providers.usage_report()["groq"]
check("prompt сложился", 10, r["prompt"])
check("completion сложился", 4, r["completion"])
check("total сложился", 14, r["total"])
check("вызов сосчитан", 1, r["calls"])

providers._usage_add("groq", "m1", {"usage": {"prompt_tokens": 5,
                                              "completion_tokens": 1,
                                              "total_tokens": 6}})
r = providers.usage_report()["groq"]
check("второй вызов прибавился", 20, r["total"])
check("модель сосчитана дважды", 2, r["models"]["m1"])

# Anthropic называет поля иначе — input/output. Молча потерять их значило бы
# считать один провайдер и обнулять другой.
providers._usage_add("anthropic", "opus", {"usage": {"input_tokens": 100,
                                                     "output_tokens": 7}})
r = providers.usage_report()["anthropic"]
check("input_tokens приняты как prompt", 100, r["prompt"])
check("output_tokens приняты как completion", 7, r["completion"])
check("total выведен из слагаемых, когда его не прислали", 107, r["total"])

# ГЛАВНОЕ: ответ без usage.
providers._usage_add("groq", "m1", {"choices": [{"message": {"content": "ok"}}]})
r = providers.usage_report()["groq"]
check("вызов без usage сосчитан в calls", 3, r["calls"])
check("вызов без usage ОБЪЯВЛЕН в без_счёта", 1, r["без_счёта"])
check("сумма от него НЕ выросла", 20, r["total"])

providers.usage_reset()
check("сброс очищает всё", {}, providers.usage_report())

print(f"\nСЧЁТ РАСХОДА: {'ЗЕЛЁНЫЙ' if fail == 0 else 'КРАСНЫЙ'} — {ok} ок, {fail} провал(ов)")
sys.exit(0 if fail == 0 else 1)
