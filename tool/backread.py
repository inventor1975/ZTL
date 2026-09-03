#!/usr/bin/env python3
# Copyright 2026 Vitaly Reznik
# SPDX-License-Identifier: Apache-2.0
"""Что ЯДРО ПРОЧИТАЛО из таблицы — словами, без модели.

ПРОМЕРЕНО, ПОТОМУ И ЗДЕСЬ. Слепой заполняющий с этим зеркалом дал 20 из 21
против 15 из 21 без него — и обошёл того, кто ВИДЕЛ эталоны (18 из 21). При
этом правил он после зеркала ОДИН документ из 24: остальное сделал сразу,
поняв на первых текстах, что ядро читает. Правило словами говорило то же
самое и не сдвинуло ничего (грунт из 17 разобранных примеров: 15 из 21).

ЗАЧЕМ. Замер 24 парадоксов показал: заполняющий понимает задачу верно и
записывает верно, но КЛАДЁТ ОТНОШЕНИЕ НЕ В ТО ПОЛЕ, и от этого зависит, какой
прибор его увидит. Промерено на одной и той же связи «ровно один из двух»:

    claim: a ^ b                      -> включается СУДЬЯ, паспорт ПУСТ
    ground: ~Tr(b) и ~Tr(a)           -> включается ПАСПОРТ, UNDERDETERMINED

Логически это одно и то же. Приборы — разные. Промпт про этот выбор молчит:
он объясняет, когда claim нужен для ЧИСЕЛ, и ничего не говорит про
пропозициональные отношения, которые не самоссылка.

Правилами словами это уже пробовали лечить — дало мало. Поэтому здесь не
правило, а ЗЕРКАЛО: заполнившему показывают, что из его таблицы вошло в разбор,
а что осталось за бортом. Увидеть, что твоя связь никуда не попала, сильнее,
чем прочитать, что так бывает.

ЧЕГО ЭТО НЕ ДЕЛАЕТ. Не говорит, что верно. Говорит, что ПРОЧИТАНО. Таблица
может быть прочитана целиком и при этом отвечать не на тот вопрос.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import zfl2  # noqa: E402

СТАТУС = {
    "verified": "проверено",
    "refuted": "опровергнуто",
    "unverified": "НЕ проверено",
    "defined": "определено формулой",
}
ПРИБОРЫ = {
    "passport": "паспорт (самоссылка, петли, разрешимость)",
    "numeric": "числовой этаж",
    "ledger": "реестр оснований",
    "epoch": "временной слой",
    "judge": "судья утверждения (claim)",
}


def прочитано(doc: dict) -> str:
    doc = zfl2.coerce(doc)
    r = zfl2.run(doc)
    строки = []

    строки.append("ЧТО ЯДРО ПРОЧИТАЛО ИЗ ВАШЕЙ ТАБЛИЦЫ")
    строки.append("")
    for i, row in enumerate(doc.get("rows") or [], 1):
        имя = row.get("name", "?")
        ст = СТАТУС.get(row.get("status"), row.get("status") or "?")
        куски = [f"  {i}. «{имя}» — {ст}"]
        if row.get("means"):
            куски.append(f"     истинно, когда: {row['means']}")
        if row.get("ground"):
            куски.append(f"     основание: {row['ground']}")
        if row.get("value") not in (None, ""):
            куски.append(f"     величина: {row['value']}")
        строки.extend(куски)
    claim = (doc.get("claim") or "").strip()
    строки.append("")
    строки.append(f"  утверждение (claim): {claim if claim else '— пусто —'}")

    применились = [k for k, v in (r.get("applies") or {}).items() if v]
    молчат = [k for k, v in (r.get("applies") or {}).items() if not v]
    строки.append("")
    строки.append("КАКИЕ ПРИБОРЫ ЭТО ЗАДЕЛО")
    if применились:
        for k in применились:
            строки.append(f"  ДА  {ПРИБОРЫ.get(k, k)}")
    else:
        строки.append("  НИ ОДИН. Таблица разобрана, и ни один прибор не нашёл,")
        строки.append("  о чём говорить: ответа не будет вообще.")
    for k in молчат:
        строки.append(f"  нет {ПРИБОРЫ.get(k, k)}")

    # ГЛАВНОЕ МЕСТО. Связь, положенная в claim, к паспорту НЕ ПОПАДАЕТ.
    if claim and not (r.get("applies") or {}).get("passport"):
        строки.append("")
        строки.append("  ВНИМАНИЕ. Отношение записано в claim, и его читает СУДЬЯ.")
        строки.append("  Паспортный прибор смотрит только основания строк, то есть")
        строки.append("  поле ground у строк со статусом «определено формулой».")
        строки.append("  Если вы хотели, чтобы связь между строками разбирал ПАСПОРТ")
        строки.append("  (петли, самоссылка, разрешимость) — её место в ground, а не")
        строки.append("  в claim. Одна и та же связь в разных полях уходит к разным")
        строки.append("  приборам, и это не опечатка, а выбор.")

    отчёт = r.get("report") or {}
    паспорт = отчёт.get("passport") or []
    if паспорт:
        строки.append("")
        строки.append("ПАСПОРТ")
        for p in паспорт:
            строки.append(f"  {', '.join(p.get('component') or [])}: {p.get('kind')}"
                          + (f" — {p.get('detail')}" if p.get("detail") else ""))
    беды = [i for i in (r.get("issues") or []) if i.get("level") == "error"]
    if беды:
        строки.append("")
        строки.append("ОШИБКИ")
        for i in беды:
            строки.append(f"  {i.get('code')} в {i.get('where')}: {i.get('hint')}")
    return "\n".join(строки)


def main() -> int:
    if len(sys.argv) < 2:
        print("backread.py <документ.json | -> ")
        return 2
    сырое = (sys.stdin.read() if sys.argv[1] == "-"
             else Path(sys.argv[1]).read_text(encoding="utf-8"))
    doc = json.loads(сырое)
    if "rows" not in doc:            # файл-набор: показать по ключу
        ключ = sys.argv[2] if len(sys.argv) > 2 else None
        d = doc.get("docs", doc)
        if ключ is None:
            print("в файле набор; второй довод — имя случая:")
            for k in list(d)[:30]:
                print("   ", k)
            return 2
        doc = d[ключ]
    print(прочитано(doc))
    return 0


if __name__ == "__main__":
    sys.exit(main())
