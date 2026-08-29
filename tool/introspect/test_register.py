#!/usr/bin/env python3
# Copyright 2026 Vitaly Reznik
# SPDX-License-Identifier: Apache-2.0
"""Стенд на РЕГИСТР ХОДА и ЖАНР — правку рубрики от 2026-08-29.

Правка родилась из прогона S-BATTERY: судья разошёлся со мной на S03 и назвал
причину — рубрика не решала T?/S без жанра. Здесь проверяется, что починка
ДЕЙСТВИТЕЛЬНО доехала до task'а и до ledger'а, а не осталась текстом в файле.

Каждая проверка идёт с КОНТРОЛЕМ: показывает не только что нужное есть, но и
что ненужное отсутствует. Без контроля «зелено» ничего не значит.
"""
import pathlib, subprocess, sys, tempfile

HERE = pathlib.Path(__file__).resolve().parent
ZC = HERE / "zchoose.py"
ok, fail = 0, 0

def check(name, cond, why=""):
    global ok, fail
    if cond: ok += 1; print(f"  OK   {name}")
    else: fail += 1; print(f"  FAIL {name} — {why}")

TEXT = ("# разбор\n\nПосле смены критерия учёта смертность в отделении "
        "снизилась вдвое.\n\nЛюбой отказ проверки лучше молчаливого пропуска.\n")

with tempfile.TemporaryDirectory() as td:
    td = pathlib.Path(td)
    src = td / "t.md"; src.write_text(TEXT, encoding="utf-8")

    # --- 1. регистр доезжает до task'а ---
    subprocess.run([sys.executable, str(ZC), "prepare", str(src), "--out", str(td/"a")],
                   check=True, capture_output=True)
    body = (td/"a"/"task-01.md").read_text(encoding="utf-8")
    check("РЕГИСТР ХОДА в task'е", "РЕГИСТР ХОДА" in body)
    check("внутренний различитель (а)/(б) назван",
          "ПОДРЫВАЕТ САМУ ЗАЯВКУ" in body and "ПЕРЕЛОЖЕН" in body)
    check("край рамки не потерян правкой", "отрезано:" in body)
    check("тэлл абсолюта жив (Любой)", "[абсолют:" in body)

    # --- 2. жанр НЕ объявлен → требование объявить развилку ---
    check("без --genre: сказано НЕ ОБЪЯВЛЕН", "ЖАНР ТЕКСТА НЕ ОБЪЯВЛЕН" in body)
    check("КОНТРОЛЬ: без --genre нет строки объявления",
          "ЖАНР ТЕКСТА ОБЪЯВЛЕН:" not in body,
          "штамп жанра просочился без флага")

    # --- 3. жанр объявлен → штамп на месте ---
    subprocess.run([sys.executable, str(ZC), "prepare", str(src), "--out", str(td/"b"),
                    "--genre", "отчёт отделения"], check=True, capture_output=True)
    body2 = (td/"b"/"task-01.md").read_text(encoding="utf-8")
    check("с --genre: жанр в task'е", "ЖАНР ТЕКСТА ОБЪЯВЛЕН: отчёт отделения" in body2)
    check("КОНТРОЛЬ: с --genre нет требования гадать",
          "ЖАНР ТЕКСТА НЕ ОБЪЯВЛЕН" not in body2)

    # --- 4. ledger видит развилку и НЕ путает её с обычной меткой ---
    vd = td / "v"; vd.mkdir()
    (vd/"verdict-01.md").write_text(
        "- «смертность снизилась вдвое» — [S|T? — зависит от жанра] — в отчёте "
        "заявка, в разборе раскрытие; отрезано: те, кого переписали в другую графу\n"
        "- «отказ лучше пропуска» — [T] — держится при расширении\n"
        "- «вложения себя не окупают» — [S] — оправдание холода; отрезано: тот, "
        "ради кого вкладывались\n", encoding="utf-8")
    subprocess.run([sys.executable, str(ZC), "assemble", str(vd), "--out", str(td/"l.md")],
                   check=True, capture_output=True)
    led = (td/"l.md").read_text(encoding="utf-8")
    check("развилка сосчитана", "Развилок по жанру: 1" in led)
    check("развилка вынесена в шапку", "ЖАНР НЕ РЕШИЛ у 1" in led)
    check("КОНТРОЛЬ: развилка НЕ засчитана в S", "S=1" in led,
          f"ожидал S=1 (только явный S), в шапке: {[l for l in led.splitlines() if 'Сводка' in l]}")
    check("КОНТРОЛЬ: обычный [S] развилкой не считается",
          led.count("Развилок по жанру: 1") == 1)
    check("края назвали у всех — жалобы нет", "КРАЙ РАМКИ НЕ НАЗВАН" not in led)

    # --- 5. развилка БЕЗ края — от улики уйти нельзя ---
    vd2 = td / "v2"; vd2.mkdir()
    (vd2/"verdict-01.md").write_text(
        "- «смертность снизилась вдвое» — [S|T? — зависит от жанра] — жанр не задан\n",
        encoding="utf-8")
    subprocess.run([sys.executable, str(ZC), "assemble", str(vd2), "--out", str(td/"l2.md")],
                   check=True, capture_output=True)
    led2 = (td/"l2.md").read_text(encoding="utf-8")
    check("развилка без «отрезано:» ловится", "КРАЙ РАМКИ НЕ НАЗВАН у 1" in led2,
          "судья ушёл от улики, объявив развилку — и это прошло молча")

print(f"\nREGISTER {'GREEN' if not fail else 'RED'}: {ok} OK, {fail} FAIL")
sys.exit(1 if fail else 0)
