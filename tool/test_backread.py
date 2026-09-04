#!/usr/bin/env python3
# Copyright 2026 Vitaly Reznik
# SPDX-License-Identifier: Apache-2.0
"""Зеркало: стенд. Без сети и без модели — оно детерминировано по построению.

Главное свойство, которое здесь проверяется, — НЕ то, что предупреждение
зажигается. А то, что оно зажигается ТОЛЬКО ТАМ, ГДЕ НАДО. Прибор, который
предупреждает всегда, перестают читать на третьем разе, и тогда он не
защищает, а создаёт чувство защиты.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from backread import прочитано, факты  # noqa: E402

ok = fail = 0


def check(имя, want, got):
    global ok, fail
    if want == got:
        ok += 1
        print(f"  [ок ] {имя}")
    else:
        fail += 1
        print(f"  [ПРОВАЛ] {имя}\n         ждали {want!r}, вышло {got!r}")


ПАРА = [{"name": "a", "means": "титул у A", "status": "unverified"},
        {"name": "b", "means": "титул у B", "status": "unverified"}]
ПЕТЛЯ = [{"name": "a", "status": "defined", "ground": "~Tr(b)"},
         {"name": "b", "status": "defined", "ground": "~Tr(a)"}]

print("ЗЕРКАЛО — ЧТО ЯДРО ПРОЧИТАЛО")

t = прочитано({"rows": ПАРА, "claim": "a ^ b"})
check("связь в claim, паспорт молчит -> ПРЕДУПРЕЖДАЕТ", True, "ВНИМАНИЕ" in t)
check("названы имена строк", True, "«a»" in t and "«b»" in t)
check("назван прибор, который взялся", True, "судья" in t)
check("сказано, что паспорт не сработал", True, "нет паспорт" in t)

t = прочитано({"rows": ПЕТЛЯ, "claim": ""})
check("та же связь в ground -> МОЛЧИТ", False, "ВНИМАНИЕ" in t)
check("паспорт назван сработавшим", True, "ДА  паспорт" in t)
check("разбор показан", True, "UNDERDETERMINED" in t)

# Пустой claim и молчащий паспорт — предупреждать не о чем: связи нет вовсе.
t = прочитано({"rows": ПАРА, "claim": ""})
check("нет связи вообще -> не предупреждает про claim", False, "ВНИМАНИЕ" in t)
check("но сказано, что не сработал НИ ОДИН прибор", True, "НИ ОДИН" in t)

# claim ЕСТЬ и паспорт СРАБОТАЛ — тоже молчим: работа дошла куда надо.
t = прочитано({"rows": ПЕТЛЯ, "claim": "a ^ b"})
check("claim при живом паспорте -> не предупреждает", False, "ВНИМАНИЕ" in t)

# Ошибки валидатора видны в зеркале, а не только в форме.
t = прочитано({"rows": [{"name": "T", "status": "defined", "ground": "Tr(T)"}],
               "claim": ""})
check("зарезервированное имя показано как ошибка", True, "E_RESERVED" in t)

# Статусы переведены, а не выведены кодом: зеркало читает человек.
t = прочитано({"rows": [{"name": "x", "status": "unverified"}], "claim": ""})
check("статус по-человечески", True, "НЕ проверено" in t)

# ФАКТЫ — та же правда СТРУКТУРОЙ. Экран рисует из них, а не из русского
# абзаца: имена приборов локализованы на семь языков, и серверный текст стал бы
# восьмым описанием. Значит структура обязана говорить ровно то же, что слова.
print("\nФАКТЫ — структура для экрана")
f = факты({"rows": ПАРА, "claim": "a ^ b"})
check("связь в claim: обход паспорта отмечен", True, f["claim_bypassed_passport"])
check("взялся судья", ["judge"], f["applied"])
check("паспорт назван молчащим", True, "passport" in f["silent"])
check("строки перенесены", ["a", "b"], [x["name"] for x in f["rows"]])
check("ошибок нет", [], f["errors"])

f = факты({"rows": ПЕТЛЯ, "claim": ""})
check("связь в ground: обхода НЕТ", False, f["claim_bypassed_passport"])
check("взялся паспорт", ["passport"], f["applied"])

f = факты({"rows": ПАРА, "claim": ""})
check("никто не взялся — сказано прямо", True, f["nothing_applied"])

f = факты({"rows": [{"name": "T", "status": "defined", "ground": "Tr(T)"}]})
check("зарезервированное имя в ошибках", ["E_RESERVED"],
      [e["code"] for e in f["errors"]])

# СЛОВА И СТРУКТУРА НЕ СМЕЮТ РАСХОДИТЬСЯ: где текст предупреждает, там и
# структура обязана поднять флаг, иначе экран и модель увидят разное.
for имя, d in [("claim", {"rows": ПАРА, "claim": "a ^ b"}),
               ("ground", {"rows": ПЕТЛЯ, "claim": ""}),
               ("пусто", {"rows": ПАРА, "claim": ""})]:
    check(f"текст и структура согласны ({имя})",
          "ВНИМАНИЕ" in прочитано(d), факты(d)["claim_bypassed_passport"])

print(f"\nЗЕРКАЛО: {'ЗЕЛЁНОЕ' if fail == 0 else 'КРАСНОЕ'} — {ok} ок, {fail} провал(ов)")
sys.exit(0 if fail == 0 else 1)
