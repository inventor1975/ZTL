#!/usr/bin/env python3
# Copyright 2026 Vitaly Reznik
# SPDX-License-Identifier: Apache-2.0
"""Отпечаток развёрнутого экземпляра: что ИМЕННО там крутится.

    python3 tool/deploy_stamp.py --write [корень]   записать отпечаток
    python3 tool/deploy_stamp.py --check [корень]   пересчитать и сверить

ЗАЧЕМ. 2026-08-29 выяснилось: дерево студии на сервере — не гит. По живому
экземпляру нельзя было сказать, какая версия крутится: ни коммита, ни тега,
только дата файла. Весь тот же день я писал наружу, что репозиторий не может
доказать состояние развёрнутого экземпляра — и это оказалось нашей собственной
дырой в проде, а не чужой.

ЧЕСТНАЯ ГРАНИЦА, И ЕЁ НАДО НАЗВАТЬ ПЕРВОЙ. Отпечаток НЕ доказывает, что версия
одобрена. Он лежит на той же машине, под тем же правом записи, что и код: кто
может править `engine.py`, тот может править и отпечаток. Это ровно граница
`drift.py`, и она здесь та же.

Что отпечаток ДАЁТ: ответ на вопрос «совпадает ли то, что лежит, с тем, что
объявлено» — и ответ этот ПЕРЕСЧИТЫВАЕТСЯ, а не читается. Объявленное без
пересчёта есть заявление, а не свидетельство; сегодня же я сам принял отказ
гита за успех, потому что не посмотрел на вывод.
"""
from __future__ import annotations

import hashlib
import json
import pathlib
import subprocess
import sys
from datetime import datetime, timezone

ИМЯ = "DEPLOYED.json"


def отпечатки(корень: pathlib.Path) -> dict[str, str]:
    """sha256 каждого .py в дереве, путями относительно корня. Порядок
    отсортирован, чтобы отпечаток не зависел от обхода файловой системы."""
    out = {}
    for p in sorted(корень.rglob("*.py")):
        if any(ч.startswith(".") or ч == "__pycache__" for ч in p.parts):
            continue
        out[str(p.relative_to(корень))] = hashlib.sha256(p.read_bytes()).hexdigest()
    return out


def версия(корень: pathlib.Path) -> str:
    """Коммит, если дерево гитовое; иначе честное «не гит»."""
    try:
        r = subprocess.run(["git", "-C", str(корень), "rev-parse", "HEAD"],
                           capture_output=True, text=True, timeout=10)
        return r.stdout.strip() if r.returncode == 0 else "НЕ ГИТ"
    except Exception:
        return "НЕ ГИТ"


def двойники(корень: pathlib.Path) -> dict[str, list[str]]:
    """Модули с ОДНИМ именем в РАЗНЫХ каталогах, которые где-то импортируются
    голым именем.

    Ловушка, стоившая вечера 2026-08-29. На сервере лежала застава по старому
    адресу `tool/introspect/admission.py`, в исходнике — по новому
    `admission/admission.py`. Долить новое, не убрав старое, значит получить ДВЕ
    заставы, и какая из них сработает, решит порядок путей, а не наш замысел.
    Такое не ловится глазом и не держится в памяти — ни в моей, ни в чужой.

    Ищем только те имена, которые ВПРАВДУ импортируются голыми (`import X`,
    `from X import ...`): одинаковые `test_*.py` в разных углах ничем не грозят,
    и ругаться на них значило бы приучить читателя не читать вывод."""
    # АРХИВЫ НЕ СЧИТАЕМ. Первый прогон выдал 15 «двойников», и почти все —
    # копии в OLD/ и _backup_pretab/, которые на путь импорта не попадают.
    # Сторож, кричащий на шум, будет проигнорирован ровно тогда, когда закричит
    # по делу; поэтому область сужена, и сужение названо вслух.
    АРХИВ = ("OLD", "attic", "_attic", "archive")
    def архивный(p: pathlib.Path) -> bool:
        return any(ч in АРХИВ or ч.startswith("_backup") for ч in p.parts)

    по_имени: dict[str, list[str]] = {}
    for p in корень.rglob("*.py"):
        if any(ч.startswith(".") or ч == "__pycache__" for ч in p.parts) or архивный(p):
            continue
        по_имени.setdefault(p.stem, []).append(str(p.relative_to(корень)))
    голые = set()
    for p in корень.rglob("*.py"):
        if any(ч.startswith(".") or ч == "__pycache__" for ч in p.parts) or архивный(p):
            continue
        try:
            src = p.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        for line in src.splitlines():
            s = line.strip()
            if s.startswith("import "):
                голые.add(s[7:].split()[0].split(".")[0].split(",")[0])
            elif s.startswith("from ") and " import " in s:
                голые.add(s[5:].split()[0].split(".")[0])
    return {имя: sorted(места) for имя, места in sorted(по_имени.items())
            if len(места) > 1 and имя in голые}


def записать(корень: pathlib.Path) -> int:
    ф = отпечатки(корень)
    (корень / ИМЯ).write_text(json.dumps({
        "at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "commit": версия(корень),
        "files": ф,
        "note": "Отпечаток НЕ доказывает одобренность: он на той же машине, "
                "под тем же правом записи, что и код. Он отвечает только на "
                "вопрос, совпадает ли лежащее с объявленным.",
    }, ensure_ascii=False, indent=1) + "\n", encoding="utf-8")
    print(f"записано {len(ф)} файлов -> {ИМЯ}  (коммит {версия(корень)})")
    return 0


def сверить(корень: pathlib.Path) -> int:
    ф = корень / ИМЯ
    if not ф.exists():
        print("ОТПЕЧАТКА НЕТ — сказать, что здесь крутится, нечем. "
              "Это отказ, а не «наверное всё в порядке».")
        return 2
    было = json.loads(ф.read_text(encoding="utf-8"))
    стало = отпечатки(корень)
    старое = было.get("files", {})
    изменены = [k for k, v in стало.items()
                if k in старое and старое[k] != v]
    новые = [k for k in стало if k not in старое]
    пропали = [k for k in старое if k not in стало]
    print(f"объявлено: {len(старое)} файлов, коммит {было.get('commit')}, "
          f"снято {было.get('at')}")
    дв = двойники(корень)
    if дв:
        print("ДВОЙНИКИ — один и тот же модуль в разных каталогах, "
              "и он импортируется голым именем:")
        for имя, места in дв.items():
            print(f"  {имя}: {', '.join(места)}")
        print("  Какой из них сработает, решит порядок путей, а не замысел.")
    if not (изменены or новые or пропали):
        print(f"СХОДИТСЯ: {len(стало)} файлов" + (f"; но ДВОЙНИКОВ {len(дв)}" if дв else ""))
        return 1 if дв else 0
    for k in изменены:
        print(f"  ИЗМЕНЁН   {k}")
    for k in новые:
        print(f"  ПОЯВИЛСЯ  {k}")
    for k in пропали:
        print(f"  ПРОПАЛ    {k}")
    print(f"РАСХОЖДЕНИЕ: {len(изменены) + len(новые) + len(пропали)}")
    return 1


def main(argv: list[str]) -> int:
    корень = pathlib.Path(argv[1]).resolve() if len(argv) > 1 else pathlib.Path(".").resolve()
    if not argv:
        print(__doc__.strip().splitlines()[0])
        return 2
    if argv[0] == "--write":
        return записать(корень)
    if argv[0] == "--check":
        return сверить(корень)
    print("нужен --write или --check")
    return 2


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
