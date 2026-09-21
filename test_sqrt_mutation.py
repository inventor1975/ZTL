# -*- coding: utf-8 -*-
"""Мутационный прогон корня: А ЛОВЯТ ЛИ ВООБЩЕ ЧТО-НИБУДЬ мои же проверки.

Зачем. `test_sqrt.py` печатает «КОРЕНЬ ЗЕЛЁНЫЙ — 10 проверок», и этому
хочется верить. Но зелёный прогон говорит только «на ЭТОМ коде проверки не
падают». Он НЕ говорит, что они упали бы на неправильном коде. Проверка,
которая не падает никогда, зелена всегда и не стоит ничего.

Поэтому здесь эталон берётся НЕ ИЗ СЕБЯ: код нарочно ломается по одному
месту, и меряется, сколько поломок проверки заметили.

    ПОЙМАНА   мутация применена, прогон упал     -> проверки живы
    ВЫЖИЛА    мутация применена, прогон зелёный  -> ДЫРА в проверках
    ЗАВИСЛА   не уложилась в срок                -> находка сама по себе

ТРИ ЗАЩИТЫ, каждая от СВОЕГО сегодняшнего провала (2026-09-21):

  1. Исходник НЕ ТРОГАЕТСЯ вовсе. Работаем на копии в песочнице. В прошлый
     раз мутация «снят потолок точности» подвесила прогон, и файл остался
     испорченным — восстанавливать пришлось из бэкапа. На копии это
     невозможно по устройству, а не по аккуратности.
  2. СРОК на каждую мутацию. Та же мутация вешала прогон на 10**(10**9) —
     не падала, а именно висела. Без срока весь прогон умирает на ней.
  3. assert на применение. Замена, которая ничего не заменила, дала бы
     зелёный прогон — и он засчитался бы как «проверки поймали». Это была
     бы ложь ровно в ту сторону, ради которой всё и затевалось.

    python3 test_sqrt_mutation.py
"""
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
TIMEOUT = 60          # с на одну мутацию; зелёный прогон занимает ~0,05 с

# (имя, что ищем, чем заменяем) — по одному месту за раз.
MUTATIONS = [
    ("потолок точности снят",
     "k = SQRT_DIGITS if k is None else min(int(k), SQRT_DIGITS_CAP)",
     "k = SQRT_DIGITS if k is None else int(k)"),

    ("верхняя граница без +1",
     "hi = Fraction(math.isqrt((n2 + q - 1) // q) + 1, s)",
     "hi = Fraction(math.isqrt((n2 + q - 1) // q), s)"),

    ("нижняя граница завышена",
     "lo = Fraction(math.isqrt(n2 // q), s)",
     "lo = Fraction(math.isqrt(n2 // q) + 1, s)"),

    ("точный корень не распознаётся",
     "if rp * rp == p and rq * rq == q:",
     "if False:"),

    ("нечётная степень единицы пропускается",
     "if any(e % 2 for e in m.values()):",
     "if False:"),

    ("степень единицы не делится пополам",
     "return _unit_str({k: e // 2 for k, e in m.items() if e})",
     "return _unit_str({k: e for k, e in m.items() if e})"),

    ("отказ на отрицательном снят",
     'if a[1] < 0:\n        raise _NoReadings("sqrt of a strictly negative quantity")',
     'if False:\n        raise _NoReadings("sqrt of a strictly negative quantity")'),

    ("метка на задевающем нуль снята",
     "if a[0] < 0:\n        return None",
     "if False:\n        return None"),

    ("вилка схлопнута в нижнюю границу",
     "return (lo[0], hi[1])",
     "return (lo[0], hi[0])"),

    ("точность подменена на грубую",
     "SQRT_DIGITS = 12",
     "SQRT_DIGITS = 2"),
]


def run_one(base, name, find, repl):
    """Одна мутация на свежей копии. Возвращает ('ПОЙМАНА'|'ВЫЖИЛА'|'ЗАВИСЛА', деталь)."""
    work = tempfile.mkdtemp(prefix="mut_")
    try:
        shutil.copytree(base, work, dirs_exist_ok=True)
        path = os.path.join(work, "znum.py")
        with open(path, encoding="utf-8") as fh:
            src = fh.read()

        # ЗАЩИТА 3: замена обязана примениться РОВНО ОДИН раз.
        n = src.count(find)
        if n != 1:
            return "НЕ ПРИМЕНЕНА", f"найдено {n} раз, ждал 1"
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(src.replace(find, repl, 1))

        try:
            p = subprocess.run([sys.executable, "test_sqrt.py"], cwd=work,
                               capture_output=True, text=True, timeout=TIMEOUT)
        except subprocess.TimeoutExpired:
            return "ЗАВИСЛА", f"не уложилась в {TIMEOUT} с"

        if p.returncode == 0:
            return "ВЫЖИЛА", "прогон остался зелёным"
        tail = [ln for ln in (p.stdout + p.stderr).splitlines() if ln.strip()]
        why = tail[-1][:70] if tail else "упала без вывода"
        return "ПОЙМАНА", why
    finally:
        shutil.rmtree(work, ignore_errors=True)


def main():
    # ЗАЩИТА 1: эталонная копия; исходник не трогается ни на одном шаге.
    base = tempfile.mkdtemp(prefix="mutbase_")
    try:
        for fn in os.listdir(HERE):
            if fn.endswith(".py"):
                shutil.copy2(os.path.join(HERE, fn), base)

        # ЗНАМЕНАТЕЛЬ: на НЕтронутой копии прогон обязан быть зелёным.
        p = subprocess.run([sys.executable, "test_sqrt.py"], cwd=base,
                           capture_output=True, text=True, timeout=TIMEOUT)
        if p.returncode != 0:
            print("НЕТРОНУТАЯ копия уже красная — мерить нечем. Стоп.")
            print((p.stdout + p.stderr)[-500:])
            return 1
        print(f"  нетронутая копия зелёная — есть от чего отсчитывать\n")

        caught = survived = hung = skipped = 0
        for name, find, repl in MUTATIONS:
            verdict, why = run_one(base, name, find, repl)
            mark = {"ПОЙМАНА": "✓", "ВЫЖИЛА": "✗ ДЫРА",
                    "ЗАВИСЛА": "⏱", "НЕ ПРИМЕНЕНА": "?"}[verdict]
            print(f"  {mark:7s} {name:38s} {why}")
            caught += verdict == "ПОЙМАНА"
            survived += verdict == "ВЫЖИЛА"
            hung += verdict == "ЗАВИСЛА"
            skipped += verdict == "НЕ ПРИМЕНЕНА"

        total = len(MUTATIONS)
        print(f"\n  ИЗ {total}: поймано {caught}, выжило {survived}, "
              f"зависло {hung}, не применено {skipped}")
        if survived or skipped:
            print("  ВЫЖИВШАЯ МУТАЦИЯ = ДЫРА В ПРОВЕРКАХ, а не успех кода.")
            return 1
        if hung:
            print("  ЗАВИСШАЯ МУТАЦИЯ — находка: поломка, которую прибор не")
            print("  отвергает, а перемалывает. Смотреть отдельно.")
        print("  МУТАЦИОННЫЙ ПРОГОН ЗЕЛЁНЫЙ — проверки корня ловят поломки.")
        return 0
    finally:
        shutil.rmtree(base, ignore_errors=True)


if __name__ == "__main__":
    raise SystemExit(main())
