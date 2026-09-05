# -*- coding: utf-8 -*-
"""Порог зелёных отпечатков в CI ставится СЧЁТОМ, а не рукой.

`.github/workflows/lean.yml` держит `test "$clean" -ge N` — дымовую проверку,
что сборка ВООБЩЕ печатает отпечатки. Число N обязано отслеживать корпус, и
`paper_claims.py` за этим следит.

ПОЧЕМУ ЭТОТ ФАЙЛ СУЩЕСТВУЕТ. За один день 2026-09-05 порог отстал ДВАЖДЫ:
одиннадцать новых модулей прибавили ~90 отпечатков, потом ещё один прибавил
шесть. Каждый раз я правил число рукой. Рука — это «знаменатель переносят, а
не считают»: ровно та ошибка, которую в тот же день вычистили из манифеста
предмета. Число, набираемое пальцами, рано или поздно наберут неверно, а
стенд, который из-за этого краснеет на каждом коммите, рано или поздно
замолчат.

Прогон без ключа — ПРОВЕРЯЕТ и падает при расхождении.
Прогон с `--fix` — СТАВИТ порог по счёту и печатает, что изменил.
"""
import os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
LEAN = os.path.join(ROOT, "lean")
YML  = os.path.join(ROOT, ".github", "workflows", "lean.yml")

r = subprocess.run(["lake", "build"], cwd=LEAN, capture_output=True, text=True)
if r.returncode != 0:
    print("СБОРКА НЕ ПРОШЛА — порог не трогаю"); print(r.stdout[-1500:]); sys.exit(2)
измерено = (r.stdout + r.stderr).count("does not depend on any axioms")

# число теорем — из аудита, для комментария рядом с порогом
a = subprocess.run([sys.executable, os.path.join(HERE, "axiom_audit.py")],
                   cwd=ROOT, capture_output=True, text=True)
m = re.search(r"ALL CLEAN: (\d+) theorems", a.stdout)
теорем = m.group(1) if m else "?"

src = open(YML, encoding="utf-8").read()
mp = re.search(r'test "\$clean" -ge (\d+)', src)
if not mp:
    print("порог в lean.yml не найден — форма файла изменилась"); sys.exit(2)
стоит = mp.group(1)

print(f"порог в lean.yml: {стоит} | измерено отпечатков: {измерено} | теорем: {теорем}")
if стоит == str(измерено):
    print("\nПОРОГ CI ЗЕЛЕНО: расхождений 0")
    sys.exit(0)
if "--fix" not in sys.argv:
    print(f"\nПОРОГ CI КРАСНО: порог {стоит} не отслеживает корпус {измерено}")
    print("   поставить счётом:  python3 inventory/ПОРОГ-CI.py --fix")
    sys.exit(1)

новый = re.sub(r'test "\$clean" -ge \d+', f'test "$clean" -ge {измерено}', src)
новый = re.sub(r"# The hand-placed prints cover \d+ names of \d+ theorems",
               f"# The hand-placed prints cover {измерено} names of {теорем} theorems",
               новый)
open(YML, "w", encoding="utf-8").write(новый)
print(f"\nПОРОГ CI ЗЕЛЕНО: поставлен счётом {стоит} -> {измерено}, расхождений 0")
