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
    # Правило «нет механизма — не достраивай»: прогон 2, судьи разошлись S/T?
    # на голом числе в заявочном регистре, и рубрика молчала.
    check("правило «нет механизма» в task'е", "НЕ ДОСТРАИВАЙ ЕГО" in body)
    check("сказано, что это T?, а не S",
          "T?, НЕ S" in body and "приговор по подозрению" in body)
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
    check("развилка сосчитана", "Развилок, где рубрика не решила: 1" in led)
    check("развилка вынесена в шапку", "РУБРИКА НЕ РЕШИЛА у 1" in led)
    check("КОНТРОЛЬ: развилка НЕ засчитана в S", "S=1" in led,
          f"ожидал S=1 (только явный S), в шапке: {[l for l in led.splitlines() if 'Сводка' in l]}")
    check("КОНТРОЛЬ: обычный [S] развилкой не считается",
          led.count("РУБРИКА НЕ РЕШИЛА у 1") == 1)
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

    # --- 6. ПРАВИЛО НАЗЫВАЕТСЯ (улучшение 1) ---
    check("закрытый список правил в task'е",
          "НАЗОВИ ПРАВИЛО" in body and "нет-правила" in body)
    check("имя «нет-предмета» в списке (дыра из случая 3)",
          "нет-предмета" in body and "НЕ ПОСТАВЛЯЕТ ЯРУСУ ИСТИНЫ" in body)
    check("КОНТРОЛЬ: есть честный выход из списка",
          "НИ ОДНО не подходит" in body,
          "список закрыт без выхода — судья выберет ближайшее и дыра спрячется")

    vd3 = td / "v3"; vd3.mkdir()
    (vd3/"verdict-01.md").write_text(
        "- «а» — [T] — рамка не тронута; правило: чисто\n"
        "- «б» — [S] — вред у соседа; отрезано: сосед; правило: б\n"
        "- «в» — [T?] — заявка без механизма; отрезано: неназванная цена; правило: нет-механизма\n"
        "- «г» — [S] — не подошло ничего; отрезано: третий; правило: нет-правила\n",
        encoding="utf-8")
    subprocess.run([sys.executable, str(ZC), "assemble", str(vd3), "--out", str(td/"l3.md")],
                   check=True, capture_output=True)
    led3 = (td/"l3.md").read_text(encoding="utf-8")
    check("правила сосчитаны", "чисто=1" in led3 and "б=1" in led3)
    check("«нет-правила» вынесено в шапку", "«НЕТ-ПРАВИЛА» у 1" in led3)
    check("КОНТРОЛЬ: жалобы на неназванное правило нет", "ПРАВИЛО НЕ НАЗВАНО" not in led3)

    vd4 = td / "v4"; vd4.mkdir()
    (vd4/"verdict-01.md").write_text("- «д» — [T] — без имени правила\n", encoding="utf-8")
    subprocess.run([sys.executable, str(ZC), "assemble", str(vd4), "--out", str(td/"l4.md")],
                   check=True, capture_output=True)
    check("неназванное правило ловится",
          "ПРАВИЛО НЕ НАЗВАНО у 1" in (td/"l4.md").read_text(encoding="utf-8"))

    # --- 7. РАЗВИЛКА ПО ЛЮБОЙ ОСИ (улучшение 3) ---
    check("развилка разрешена по любой оси", "не решает:" in body)
    vd5 = td / "v5"; vd5.mkdir()
    (vd5/"verdict-01.md").write_text(
        "- «е» — [S|T — не решает: свойство хода или ставки] — отрезано: проигравший; правило: нет-правила\n"
        "- «ж» — [Z] — абсолют; правило: абсолют\n", encoding="utf-8")
    subprocess.run([sys.executable, str(ZC), "assemble", str(vd5), "--out", str(td/"l5.md")],
                   check=True, capture_output=True)
    led5 = (td/"l5.md").read_text(encoding="utf-8")
    check("развилка S|T (не жанровая) сосчитана", "Развилок, где рубрика не решила: 1" in led5)
    check("шапка говорит «рубрика не решила»", "РУБРИКА НЕ РЕШИЛА у 1" in led5)
    check("КОНТРОЛЬ: соседняя обычная метка не съедена развилкой", "Z=1" in led5)

    # --- 8. МНОГОСТРОЧНЫЙ ХОД: «отрезано» и «правило» на продолжении с отступом ---
    vd6 = td / "v6"; vd6.mkdir()
    (vd6/"verdict-01.md").write_text(
        "- «з» — [S] — вред переложен на соседа,\n"
        "  и заявка при этом стоит.\n"
        "  отрезано: сосед, которого не спрашивали\n"
        "  правило: б\n"
        "\n"
        "Здесь идёт обычная проза, а не ход. правило: нет-правила\n",
        encoding="utf-8")
    subprocess.run([sys.executable, str(ZC), "assemble", str(vd6), "--out", str(td/"l6.md")],
                   check=True, capture_output=True)
    led6 = (td/"l6.md").read_text(encoding="utf-8")
    check("многострочный ход: край с продолжения зачтён",
          "КРАЙ РАМКИ НЕ НАЗВАН" not in led6,
          "«отрезано» на продолжении не увидено — судью обвинят в чужой вине")
    check("многострочный ход: правило с продолжения зачтено",
          "ПРАВИЛО НЕ НАЗВАНО" not in led6 and "б=1" in led6)
    # Искать надо в СВОДКЕ ШАПКИ, а не во всём файле: ledger дословно несёт и
    # тело вердикта, где слово «нет-правила» стоит в прозе законно. Первая
    # версия этой проверки падала на этом и обвиняла исправный сборщик.
    сводка = next(l for l in led6.splitlines() if l.startswith("Правила, по которым"))
    check("КОНТРОЛЬ: неотступленная проза в ход НЕ втянута",
          "нет-правила" not in сводка and "б=1" in сводка,
          f"«правило:» из соседнего абзаца зачлось ходу; сводка: {сводка}")

    # --- 9. ХОД НУМЕРОВАННЫМ ПУНКТОМ, не буллетом ---
    vd7 = td / "v7"; vd7.mkdir()
    (vd7/"verdict-01.md").write_text(
        "1. «и» — [E] — судить не на чем\n"
        "   правило: нет-правила\n"
        "2) «к» — [S] — вред за краем; отрезано: третий\n"
        "   правило: б\n", encoding="utf-8")
    subprocess.run([sys.executable, str(ZC), "assemble", str(vd7), "--out", str(td/"l7.md")],
                   check=True, capture_output=True)
    led7 = (td/"l7.md").read_text(encoding="utf-8")
    check("нумерованный ход сосчитан", "E=1" in led7 and "S=1" in led7,
          "сборщик принимал только буллет и молча отдавал пустую сводку")
    check("правило с нумерованного хода зачтено",
          "ПРАВИЛО НЕ НАЗВАНО" not in led7 and "б=1" in led7)

    # --- 10. ход в жирном оформлении; метка в ПРОДОЛЖЕНИИ нового хода не открывает ---
    vd8 = td / "v8"; vd8.mkdir()
    (vd8/"verdict-01.md").write_text(
        "**Ход 1.** «л» — **[E]** — судить не на чем\n"
        "   правило: нет-правила\n"
        "**2.** «м» — [S] — вред за краем; отрезано: третий\n"
        "   здесь в продолжении упомянута метка [T], и она НЕ должна открыть ход\n"
        "   правило: б\n", encoding="utf-8")
    subprocess.run([sys.executable, str(ZC), "assemble", str(vd8), "--out", str(td/"l8.md")],
                   check=True, capture_output=True)
    led8 = (td/"l8.md").read_text(encoding="utf-8")
    сводка8 = next(l for l in led8.splitlines() if "Сводка меток" in l)
    check("жирный/нумерованный ход сосчитан", "E=1" in сводка8 and "S=1" in сводка8,
          f"сводка: {сводка8}")
    check("КОНТРОЛЬ: метка в продолжении нового хода не открыла",
          "T=1" not in сводка8, f"продолжение засчиталось как ход; сводка: {сводка8}")

    # --- 11. ЧТО СЧИТАТЬ ЗАЯВКОЙ (четвёртая дыра, вскрыта чужими судьями) ---
    check("вопрос о заявке в task'е", "ЧТО СЧИТАТЬ ЗАЯВКОЙ" in body)
    check("обе стороны названы и различены",
          "ПОКАЗАНИЕ" in body and "ПОЛОЖЕНИЕ ДЕЛ" in body
          and "изменился УЧЁТ, а не мир" in body)
    check("КОНТРОЛЬ: неразличимый случай объявляется развилкой, а не выбирается",
          "это РАЗВИЛКА, а не выбор" in body,
          "без этого судья снова выберет вопрос сам")
    check("требование вписано в форму ответа",
          "заявка: показание|положение дел" in body)

print(f"\nREGISTER {'GREEN' if not fail else 'RED'}: {ok} OK, {fail} FAIL")
sys.exit(1 if fail else 0)
