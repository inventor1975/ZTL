# -*- coding: utf-8 -*-
"""Всякое имя, названное в статье, обязано существовать в корпусе.

Ловит расхождение текста и кода в ОБЕ стороны: и ссылку на несуществующую
теорему (завышение), и модуль, о котором статья молчит (занижение — ровно то,
что нашлось 2026-09-05: семь разделов стояли MEASURED при живых модулях).
Счёт ведёт прибор, не глаз.
"""
import os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.join(os.path.dirname(HERE), "lean")
PAPER = os.path.join(os.path.dirname(HERE), "paper", "ZTL-draft_1.4.md")

модули = {f[:-5] for f in os.listdir(LEAN) if f.endswith(".lean")}
имена = set()
for m in модули:
    src = open(os.path.join(LEAN, m + ".lean"), encoding="utf-8").read()
    depth = 0
    for line in src.split("\n"):
        s = line.strip()
        о, з = s.count("/-"), s.count("-/")
        внутри = depth > 0
        depth = max(0, depth + о - з)
        if внутри or о or s.startswith("--"):
            continue
        d = re.match(r"^(?:private\s+|protected\s+)?(?:theorem|lemma|def|abbrev|structure|inductive)\s+([A-Za-z_][\w'.!?]*)", s)
        if d:
            имена.add(d.group(1))

текст = open(PAPER, encoding="utf-8").read()
ссылки_мод = set(re.findall(r"`([A-Z][A-Za-z_]*)\.lean`", текст))
ссылки_имён = set(re.findall(r"`([a-z_][\w']*)`", текст))

нет_модуля = sorted(ссылки_мод - модули)
# имена проверяем только те, что похожи на наши (есть в корпусе хоть где-то
# ИЛИ выглядят как snake_case-теорема): иначе поймаем обычные слова
кандидаты = {n for n in ссылки_имён if "_" in n}
чужие = sorted(кандидаты - имена)

# ЛОЖНАЯ ТРЕВОГА, НАЙДЕННАЯ НА ПЕРВОМ ЖЕ ПРОГОНЕ. Статья называет и ЯДРОВЫЕ
# имена — обычно как раз те, которых мы ИЗБЕГАЕМ (`length_replicate` тянет
# propext). Прибор их не знал и объявлял отсутствующими. Спрашиваем компилятор,
# а не гадаем: имя, которое Lean разрешает, — не наша дыра.
нет_имени = []
if чужие:
    import subprocess, tempfile
    зонд = "\n".join(
        f"#check @{pre}{n}" for n in чужие
        for pre in ("", "List.", "Nat.", "Bool.", "V."))
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False,
                                     encoding="utf-8") as f:
        f.write("import ZTL\n" + зонд + "\n"); проба = f.name
    out = subprocess.run(["lake", "env", "lean", проба], cwd=LEAN,
                         capture_output=True, text=True).stdout
    for n in чужие:
        разрешилось = any(f"@{pre}{n}" in out and "unknown" not in out.split(f"@{pre}{n}")[0][-200:]
                          for pre in ("", "List.", "Nat.", "Bool.", "V."))
        # надёжнее: имя ядровое, если хоть один префикс НЕ дал unknownIdentifier
        плохие = out.count(f"`{n}`") + sum(out.count(f"`{pre}{n}`") for pre in ("List.", "Nat.", "Bool.", "V."))
        if плохие >= 5:
            нет_имени.append(n)

print(f"модулей в корпусе: {len(модули)} | имён объявлено: {len(имена)}")
print(f"ссылок на модули в статье: {len(ссылки_мод)} | snake_case-имён: {len(кандидаты)}")
print()
if нет_модуля:
    print("НАЗВАН В СТАТЬЕ, НЕТ В КОРПУСЕ (модули):")
    for m in нет_модуля: print("   ", m)
else:
    print("модули: все названные существуют")
if нет_имени:
    print("НАЗВАН В СТАТЬЕ, НЕТ В КОРПУСЕ (имена):")
    for n in нет_имени: print("   ", n)
else:
    print("имена: все названные существуют")
# ОДНА МАРКА, КОТОРАЯ НЕ МОЖЕТ ПОЯВИТЬСЯ ПРИ ПРОВАЛЕ. Прежде я собирался
# закрепить в раннере строку «все названные существуют» — а она печатается
# ОТДЕЛЬНО для модулей и для имён, значит при провале одной половины вторая
# всё равно дала бы марку. Раннер спасал бы код возврата, но марка, которая
# держится на чужой подстраховке, — не марка.
расхождений = len(нет_модуля) + len(нет_имени)
if расхождений == 0:
    print(f"\nСВЕРКА ССЫЛОК ЗЕЛЕНО: модулей {len(ссылки_мод)}, "
          f"имён {len(кандидаты)}, расхождений 0")
else:
    print(f"\nСВЕРКА ССЫЛОК КРАСНО: расхождений {расхождений}")
sys.exit(1 if расхождений else 0)
