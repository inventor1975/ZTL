# -*- coding: utf-8 -*-
"""Договор ПРЕДСТАВЛЕНИЯ между перечислителем и проверяющим членство.

ДИАГНОЗ УТОЧНЁН 2026-08-31 (внешний рецензент). Неверно было бы сказать «git слеп к
кириллице»: git видел файл прекрасно. Сторож ПОТРЕБИЛ экранированное
представление git как буквальный путь.

    РАЗРЯД: РАСХОЖДЕНИЕ ПРЕДСТАВЛЕНИЙ / ЛОЖНОЕ ПОКРЫТИЕ
      производитель отдаёт экранированный путь
      -> сторож считает его буквальным Unicode-путём
      -> отслеживаемый артефакт объявлен ОТСУТСТВУЮЩИМ

Лечение — не «поддержать кириллицу», а ОПРЕДЕЛИТЬ И ИСПЫТАТЬ договор
представления между командой перечисления и проверкой членства.

Здесь он испытывается на шести видах имён, и на КАЖДОМ прогоне есть
заведомо присутствующий и заведомо отсутствующий контроль.
"""
import os, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def tracked(quote_path):
    args = ["git", "-C", ROOT]
    if not quote_path:
        args += ["-c", "core.quotePath=false"]
    args += ["ls-files"]
    r = subprocess.run(args, capture_output=True, text=True)
    return set(r.stdout.splitlines())


def main():
    print("=" * 66)
    print("ДОГОВОР ПРЕДСТАВЛЕНИЯ ПУТЕЙ — перечислитель против проверяющего")
    print("=" * 66)
    good = tracked(quote_path=False)
    bad = tracked(quote_path=True)

    # ЗАВЕДОМО ПРИСУТСТВУЮЩИЕ, шесть видов имён
    present = [
        ("ASCII", "run_all.py"),
        ("кириллица", "inventory/tau_airline/СТАРШИНСТВО.py"),
        ("кириллица+дефисы", "inventory/oic_seam/ЖУРНАЛ-ПОПРАВОК.md"),
        ("смешанное", "inventory/tau_airline/УБИТЫЙ-ПУТЬ-003_детектор.md"),
        ("вложенный ASCII", "tool/warrant_receipt.py"),
        ("расширение .lean", "lean/NoGift.lean"),
    ]
    absent = ("ЗАВЕДОМО ОТСУТСТВУЮЩИЙ", "inventory/такого-файла-нет-12345.py")

    fails = []
    print("\nЗАВЕДОМО ПРИСУТСТВУЮЩИЕ:")
    for kind, p in present:
        on_disk = os.path.exists(os.path.join(ROOT, p))
        ok_new, ok_old = p in good, p in bad
        mark = "ок" if ok_new else "ПРОВАЛ"
        note = "" if ok_new == ok_old else "  <- СТАРЫЙ сторож здесь ошибался"
        print(f"  {kind:<18} на диске={on_disk} новый={ok_new} старый={ok_old} {mark}{note}")
        if on_disk and not ok_new:
            fails.append(f"{kind}: отслеживаемый файл не опознан")

    print("\nЗАВЕДОМО ОТСУТСТВУЮЩИЙ (контроль в другую сторону):")
    kind, p = absent
    seen = p in good
    print(f"  {kind:<18} опознан как присутствующий={seen} "
          f"{'ПРОВАЛ' if seen else 'ок'}")
    if seen:
        fails.append("несуществующий файл объявлен присутствующим")

    print("\n" + "=" * 66)
    if fails:
        print("ДОГОВОР ПРЕДСТАВЛЕНИЯ КРАСНЫЙ:")
        for f in fails:
            print("  -", f)
        return 1
    print("ДОГОВОР ПРЕДСТАВЛЕНИЯ ЗЕЛЁНЫЙ — сторож опознаёт и присутствие,")
    print("и отсутствие, на всех испытанных видах имён.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
