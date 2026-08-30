# -*- coding: utf-8 -*-
"""ASSURANCE-INCIDENT-001 — самосогласованность, выданная за защиту от подделки.

ЧТО СЛУЧИЛОСЬ. ОТОЗВАНО всё, что ниже в кавычках. В ночь на 2026-08-31 я
привёл внешнему рецензенту квитанцию как довод, сказав, что вердикт «проверяется на той
стороне». То же объявлял зелёный заголовок стенда `tool/test_warrant_receipt.py`,
то же обещал докстринг `verify()`: «изменение ЛЮБОГО из пяти полей меняет
отпечаток и валит сверку». Ни код, ни стенд такого свойства не имели.

ПОЧЕМУ ЭТО ХУЖЕ ОБЫЧНОГО БАГА. Стенд был ЗЕЛЁНЫЙ и объявлял свойство
безопасности, которого в коде нет, — и я цитировал его зелёную строку как
свидетельство. Негодный оракул опаснее отсутствующего: отсутствующий не врёт.

КОММИТ, ГДЕ ЛОЖНЫЙ ЗЕЛЁНЫЙ ЖИВ: 6536d1492000a3988815abf9ed175f5d417b7c19

=====================================================================
ПОЧЕМУ ЭТОТ ФАЙЛ НИЧЕГО НЕ ИМПОРТИРУЕТ — вторая правка, 2026-08-31
=====================================================================
Первая моя редакция звала ЖИВОЙ `verify()`. внешний рецензент поймал: тогда правильная
починка уязвимости ПОЛОЖИТ этот стенд, и один файл начнёт отвечать на два
несовместимых вопроса. Это ровно тот разряд «ЛОЖНЫЙ ПРЕДМЕТ», который он
назвал сообщением раньше, — и я его тут же и совершил.

Поэтому исторический `_canon`, `_sha` и `verify` ВПИСАНЫ СЮДА ДОСЛОВНО из
6536d14, и живой модуль не трогается вовсе. Разделены два утверждения:

  ИСТОРИЧЕСКОЕ (этот файл): на 6536d14 подделка с пересчётом ПРОХОДИЛА.
      Обязано воспроизводиться ВЕЧНО. Красный тут значит, что переписали
      историю, а не что чинить нечего.
  ТЕКУЩЕЕ (отдельный стенд, которого ещё нет): нынешняя проверка подделку
      ОТВЕРГАЕТ. Состояние — НЕ УСТАНОВЛЕНО, до выбора модели доверия.

Один стенд на два вопроса — снова негодный оракул.
"""
import json, hashlib, sys

# =====================================================================
# КРИПТОГРАФИЧЕСКАЯ ПРИВЯЗКА К ИСТОРИИ — по требованию внешнего рецензента 2026-08-31
# =====================================================================
# Ручная копия может УПЛЫТЬ. Историческое утверждение не «эта копия функции
# уязвима», а «реализация НА КОММИТЕ 6536d14 имела это свойство». Значит
# копию надо привязать к оригиналу так, чтобы поздняя «уборка» её не
# превратила молча в «представительную».
#
# Проверить оригинал руками:
#   git show 6536d14:tool/warrant_receipt.py | sha256sum
HIST_COMMIT   = "6536d1492000a3988815abf9ed175f5d417b7c19"
HIST_PATH     = "tool/warrant_receipt.py"
HIST_BLOB     = "73f8b42fc50aaffd480562881945c65b2d026133"
HIST_FILE_SHA = "456d630f302442af8fddd1a35f9c51d03adb20a3811b69736e4038cbe3dabdbd"
# ДВЕ РАЗНЫЕ ВЕЛИЧИНЫ, И ПУТАТЬ ИХ НЕЛЬЗЯ.
#
# HIST_FUNCS_SHA — отпечаток трёх функций, ВЫРЕЗАННЫХ ИЗ ИСТОРИЧЕСКОГО файла
# процедурой ниже. Воспроизводится так:
#   git show 6536d14:tool/warrant_receipt.py | python3 -c "import sys,hashlib,re; \
#     s=sys.stdin.read(); print(hashlib.sha256('\\n'.join( \
#     re.search(r'^def '+n+r'\(.*?(?=\n\ndef |\n\n#|\Z)',s,re.S|re.M).group(0) \
#     for n in ['_canon','_sha','verify']).encode()).hexdigest())"
HIST_FUNCS_SHA = "f69b9a3968283a4a27e5c18e5e410bcec336fdc960b0e9df9b6bdc08732eb2d6"
#
# COPY_SHA — отпечаток ЗДЕШНЕЙ копии, снятый её же процедурой. Он ДРУГОЙ и
# обязан быть другим: копия переименована (_hist) и живёт в другом файле.
# Подгонять одно под другое было бы ровно тем подлогом, который тут и
# расследуется. Сходство копии с оригиналом установлено РУКАМИ один раз, на
# этом коммите; здесь стенд стережёт лишь то, что КОПИЮ потом не правили.
COPY_SHA = "3edc1e59a87c9e530dbdeff704ec4c519a97457838efc6686ebc06985949021b"

# --------- ЗАМОРОЖЕНО ИЗ 6536d14, дословно. НЕ ПРАВИТЬ вместе с живым кодом.
def _canon_hist(obj) -> str:
    return json.dumps(obj, ensure_ascii=False, sort_keys=True,
                      separators=(",", ":"))


def _sha_hist(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _verify_hist(rec: dict) -> bool:
    core = {k: v for k, v in rec.items() if k != "digest"}
    return rec.get("digest") == _sha_hist(_canon_hist(core))
# --------- конец замороженного

# Образец тоже ЗАМОРОЖЕН: строить его живым receipt() значило бы снова
# привязать историческое утверждение к сегодняшнему коду.
SPECIMEN_CORE = {
    "version": "warrant-receipt-0.1",
    "registry": None,
    "derived_from": None,
    "claim": "клиент установлен",
    "holding": {"b": "Z"},
    "grounds": {"a": {"status": "verified", "ground": "паспорт"}},
    "verdict": {"value": "T", "disposition": "ESTABLISHED", "grade": "A",
                "credit": "REDEEMABLE", "unredeemable": []},
    "epoch": "E17",
    "expiry": None,
    "on_stipulation": None,
}


def _fixture_selfcheck():
    """Копия обязана совпасть с историей ДО того, как что-то утверждать."""
    import inspect
    joined = "\n".join(
        inspect.getsource(f).replace("_hist", "").rstrip()
        for f in (_canon_hist, _sha_hist, _verify_hist))
    return hashlib.sha256(joined.encode()).hexdigest()


def main():
    print(f"ПРИВЯЗКА: коммит {HIST_COMMIT[:7]}, blob {HIST_BLOB[:12]}")
    print(f"  sha256 исторического файла : {HIST_FILE_SHA[:16]}…")
    print(f"  sha256 замороженного образца: "
          f"{hashlib.sha256(_canon_hist(SPECIMEN_CORE).encode()).hexdigest()[:16]}…")
    now = _fixture_selfcheck()
    print(f"  отпечаток здешней копии    : {now[:16]}…")
    if now != COPY_SHA:
        print()
        print("СТЕНД КРАСНЫЙ: копию исторических функций ПРАВИЛИ.")
        print(f"  пришпилено: {COPY_SHA}")
        print(f"  сейчас    : {now}")
        print("Историческое утверждение опирается на неизменность этой копии.")
        return 1
    print("  копия не тронута с момента заморозки.")
    print()
    genuine = {**SPECIMEN_CORE,
               "digest": _sha_hist(_canon_hist(SPECIMEN_CORE))}
    fails = []

    print("ИСТОРИЧЕСКАЯ РЕАЛИЗАЦИЯ 6536d14 — живой модуль не тронут\n")

    print("1. ПОДЛИННАЯ КВИТАНЦИЯ")
    ok = _verify_hist(genuine)
    print(f"   verify -> {ok}")
    if not ok:
        fails.append("подлинная не прошла — образец разошёлся с историей")

    print("\n2. ПОРЧА БЕЗ ПЕРЕСЧЁТА — обязана упасть")
    bad = json.loads(json.dumps(genuine))
    bad["claim"] = "клиент НЕ установлен"
    ok2 = _verify_hist(bad)
    print(f"   verify -> {ok2}")
    if ok2:
        fails.append("порча без пересчёта прошла — нет и адресации")

    print("\n3. ПОДДЕЛКА С ПЕРЕСЧЁТОМ — вот оно, происшествие")
    forged = json.loads(json.dumps(genuine))
    forged["claim"] = "клиент НЕ установлен"
    forged["verdict"]["disposition"] = "REFUSED"
    forged["epoch"] = "E99"
    core = {k: v for k, v in forged.items() if k != "digest"}
    forged["digest"] = _sha_hist(_canon_hist(core))
    ok3 = _verify_hist(forged)
    print("   подменены claim, disposition и epoch, отпечаток пересчитан")
    print(f"   verify -> {ok3}")
    if not ok3:
        fails.append("подделка НЕ прошла — историю переписали, разбираться")

    print("\n4. КВИТАНЦИЯ, СОЧИНЁННАЯ С НУЛЯ")
    scratch = {**SPECIMEN_CORE, "claim": "что угодно"}
    scratch = {**scratch, "digest": _sha_hist(_canon_hist(scratch))}
    ok4 = _verify_hist(scratch)
    print(f"   verify -> {ok4}")
    if not ok4:
        fails.append("сочинённая не прошла — неожиданно")

    print("\n" + "=" * 68)
    if fails:
        print("ИНЦИДЕНТ-СТЕНД КРАСНЫЙ:")
        for f in fails:
            print("  -", f)
        return 1
    print("ASSURANCE-INCIDENT-001 ВОСПРОИЗВЕДЁН.")
    print("Подделка с пересчётом отпечатка ПРОХОДИТ сверку (пункт 3),")
    print("и квитанция, сочинённая с нуля, тоже (пункт 4).")
    print()
    print("УСТАНОВЛЕНО НА ТОЙ ВЕРСИИ: детерминированная каноническая")
    print("адресация по содержимому — и только она.")
    print("СВОЙСТВО НЫНЕШНЕГО КОДА ЭТОТ СТЕНД НЕ ПРОВЕРЯЕТ И НЕ УТВЕРЖДАЕТ.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
