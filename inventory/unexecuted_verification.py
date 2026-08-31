# -*- coding: utf-8 -*-
"""UNEXECUTED VERIFICATION PATH — ищем НАШИ инструкции проверки, которые не работают.

РАЗРЯД ДЕФЕКТА (формулировка внешнего рецензента, 2026-08-31):
    задокументированный путь проверки → выглядит исполнимым → на самом деле
    не был воспроизведён на том состоянии, которое сам называет.

ФАЛЬСИФИКАТОР: инструкция перепроверки не считается исполнимым свидетельством,
пока ТА САМАЯ команда не отработала успешно против ТОГО САМОГО пина, который
она называет.

ДВА ИЗВЕСТНЫХ СЛУЧАЯ, ради которых прибор и заведён:
  1. `CONFORMANCE-v0.1` (наш): велит взять `e819dec7` и запустить
     verify_fixtures.py; на том коммите `judge()` ещё нет, команда падает.
     Нашли не мы — нашёл OIC.
  2. ASSURANCE-INCIDENT-001 (наш, 2026-08-31): зелёный стенд объявлял защиту
     от подделки, которой в коде нет.

Два случая — это ДВА СЛУЧАЯ, а не «класс». внешний рецензент прав: сперва посчитать.

ЧТО ПРИБОР ДЕЛАЕТ. Находит в корпусе блоки команд, называющие ПИН (тег или
коммит), и для каждого проверяет ДЕШЁВУЮ необходимую предпосылку: существует
ли пин и существует ли на нём файл, который команда запускает. Это ловит ровно
ту беду, что случилась с v0.1, не прогоняя команды целиком.

ЕГО ПОТОЛОК, названный вслух: прибор проверяет НЕОБХОДИМОЕ условие, а не
достаточное. Пин на месте и файл на месте — команда всё ещё может падать.
Значит найденное — нижняя оценка, и «ноль» здесь не означает «всё исполнимо».
"""
import os, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SKIP_DIRS = {".git", "_attic", "archive", "OLD", ".lake", "node_modules",
             "__pycache__", "fixtures", "lab", ".claude"}
CHECKOUT = re.compile(r"git\s+checkout\s+([A-Za-z0-9._/-]+)")
RUNS = re.compile(r"(?:python3?|lake\s+env\s+lean)\s+([A-Za-z0-9._/-]+\.(?:py|lean))")

# ПОЛОЖИТЕЛЬНЫЙ КОНТРОЛЬ ЗАСТАВИЛ ПЕРЕПИСАТЬ. Первая редакция проверяла только
# «существует ли ВЫЗЫВАЕМЫЙ файл на пине» и известный случай НЕ НАХОДИЛА:
# у v0.1 вызываемый скрипт лежит в чужом репозитории, а падает ИМПОРТ нашего
# модуля `ztljudge`, которого на пине e819dec7 ещё нет (там ztltool.py;
# переименование в c858429). Прибор, не находящий известное присутствие,
# удостоверять отсутствие не вправе — поэтому проверяем ещё и ТОЧКИ ВХОДА.
ENTRYPOINTS = {"ztljudge": "ztljudge.py", "zverify": "zverify.py"}


WINDOWS = {}


def window_of(path, pin):
    return WINDOWS.get((path, pin), "")


def git(*args):
    r = subprocess.run(["git", "-C", ROOT] + list(args),
                       capture_output=True, text=True)
    return r.returncode, r.stdout.strip()


def positive_control():
    """Прибор обязан находить ИЗВЕСТНОЕ присутствие, иначе его ноль ничего не стоит.

    Известный случай: конформанс v0.1 велит взять `downstream-ztl-input-v0.1.1-signed`
    (= e819dec7) и опереться на `ztljudge`, которого на том пине ещё нет — там
    `ztltool.py`, переименование в `c858429`. Проверяем это КАЖДЫЙ прогон.
    """
    pin = "downstream-ztl-input-v0.1.1-signed"
    code, _ = git("rev-parse", "--verify", f"{pin}^{{commit}}")
    if code != 0:
        return False, f"пин {pin} не найден — контроль несостоятелен"
    c2, _ = git("cat-file", "-e", f"{pin}:ztljudge.py")
    if c2 == 0:
        return False, "ztljudge.py НА ПИНЕ ЕСТЬ — известный случай исчез, прибор не проверен"
    c3, _ = git("cat-file", "-e", f"{pin}:ztltool.py")
    if c3 != 0:
        return False, "ztltool.py на пине тоже нет — история не та, разбираться"
    return True, "известный случай найден: ztljudge отсутствует, ztltool на месте"


def main():
    ok_ctl, why = positive_control()
    print("=" * 68)
    print("ПОЛОЖИТЕЛЬНЫЙ КОНТРОЛЬ:", "ПРОЙДЕН" if ok_ctl else "ПРОВАЛЕН")
    print(" ", why)
    if not ok_ctl:
        print("\nПрибор не показал, что умеет находить известное присутствие.")
        print("Любой его «ноль» ниже — НЕ свидетельство. Прогон недействителен.")
        return 1
    blocks = []
    for base, dirs, names in os.walk(ROOT):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
        for n in names:
            if not n.endswith((".md", ".txt")):
                continue
            path = os.path.join(base, n)
            try:
                text = open(path, encoding="utf-8", errors="replace").read()
            except Exception:
                continue
            for m in CHECKOUT.finditer(text):
                pin = m.group(1)
                window = text[m.end():m.end() + 600]
                runs = RUNS.findall(window)
                rel = os.path.relpath(path, ROOT)
                WINDOWS[(rel, pin)] = window
                blocks.append((rel, pin, runs))

    print("=" * 68)
    print("UNEXECUTED VERIFICATION PATH — перепись по корпусу")
    print("=" * 68)
    print(f"\nнайдено блоков «checkout ПИН + запуск»: {len(blocks)}")
    if not blocks:
        print("НОЛЬ БЛОКОВ — это отказ поиска, а не свойство корпуса.")
        return 2

    bad, unknown, ok = [], [], 0
    for path, pin, runs in blocks:
        code, _ = git("rev-parse", "--verify", f"{pin}^{{commit}}")
        if code != 0:
            unknown.append((path, pin, "пин не найден в этом репозитории"))
            continue
        for f in runs:
            c2, _ = git("cat-file", "-e", f"{pin}:{f}")
            if c2 != 0:
                bad.append((path, pin, f))
            else:
                ok += 1
        # точки входа, УПОМЯНУТЫЕ рядом с командой, обязаны быть на пине
        for mod, fname in ENTRYPOINTS.items():
            if mod in window_of(path, pin):
                c3, _ = git("cat-file", "-e", f"{pin}:{fname}")
                if c3 != 0:
                    bad.append((path, pin, f"импорт {mod} ({fname})"))
                else:
                    ok += 1
        if not runs:
            unknown.append((path, pin, "пин есть, запускаемого файла в окне не видно"))

    print(f"  пин есть и запускаемый файл на нём есть : {ok}")
    print(f"  ПИН ЕСТЬ, А ФАЙЛА НА НЁМ НЕТ           : {len(bad)}")
    print(f"  не определилось                        : {len(unknown)}")

    if bad:
        print("\nНАЙДЕННЫЕ НЕИСПОЛНИМЫЕ ПУТИ:")
        for path, pin, f in bad:
            print(f"  {path}: checkout {pin} -> {f} НА ЭТОМ ПИНЕ ОТСУТСТВУЕТ")
    if unknown:
        print("\nНЕ ОПРЕДЕЛИЛОСЬ (не выводы, а работа для человека):")
        for path, pin, why in unknown[:8]:
            print(f"  {path}: {pin} — {why}")
        if len(unknown) > 8:
            print(f"  … и ещё {len(unknown)-8}")

    print("\nПОТОЛОК: проверено НЕОБХОДИМОЕ условие, не достаточное.")
    print("Ноль в средней строке НЕ означает «все пути исполнимы».")
    print("Это НИЖНЯЯ оценка распространённости разряда.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
