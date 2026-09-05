# -*- coding: utf-8 -*-
"""Ярус четвёртого правила параметрических таблиц — ПРОМЕР, не предсказание.

§27 просит порт γ/δ-таблиц. Прежде чем его начинать, здесь измерено, на каком
ярусе аксиом стоит надёжность самих четырёх правил.

    γ₁  T:∀xφ → T:φ(c)     пустой список
    γ₂  F:∃xφ → N:φ(c)     пустой список   (¬∃→∀¬ конструктивно)
    δ₁  T:∃xφ → T:φ(c*)    пустой список   (исключение ∃ конструктивно)
    δ₂  F:∀xφ → N:φ(c*)    КЛАССИЧЕСКИЙ    (нужно ¬∀→∃¬)

Первые три живут в корпусе (`lean/ZParamSound.lean`). Четвёртое НЕ живёт: оно
сломало бы инвариант «всё на пустом списке», а исключение в аудите — это место,
где спрячется настоящая тревога. Оно лежит в `probes/` и меряется здесь.

СТЕНД ОБЯЗАН ПАДАТЬ В ОБЕ СТОРОНЫ. Если четвёртое вдруг соберётся на пустом
списке — значит нашёлся бесвыборный путь, и это НАХОДКА, а не повод молчать.
Если первые три перестанут быть чистыми — тем более.

Что тут НЕ утверждается: что бесвыборного пути не существует. Он не найден
стандартным доводом, и это всё, что промер даёт.
"""
import os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.join(os.path.dirname(HERE), "lean")
ЗОНД = os.path.join(HERE, "probes", "delta_all_classical.lean")

def аксиомы(файл, имена):
    r = subprocess.run(["lake", "env", "lean", файл], cwd=LEAN,
                       capture_output=True, text=True)
    if r.returncode != 0:
        print("СБОРКА НЕ ПРОШЛА:"); print(r.stdout[-2000:]); print(r.stderr[-2000:])
        sys.exit(2)
    из = {}
    for line in r.stdout.split("\n"):
        m = re.match(r"'([\w.]+)' (?:depends on axioms: \[(.*)\]|does not depend on any axioms)", line)
        if m:
            из[m.group(1).split(".")[-1]] = set(
                x.strip() for x in (m.group(2) or "").split(",") if x.strip())
    return {и: из.get(и) for и in имена}

модуль = os.path.join(LEAN, "ZParamSound.lean")
чистые = аксиомы(модуль, ["gamma_all", "gamma_ex", "delta_ex",
                          "delta_all_constructive", "gamma_delta_sound_three"])
классика = аксиомы(ЗОНД, ["delta_all_classical"])

ЖДЁМ_КЛАССИКУ = {"propext", "Classical.choice", "Quot.sound"}
беды = []
for и, ax in чистые.items():
    if ax is None:
        беды.append(f"{и}: не найдено в выводе")
    elif ax:
        беды.append(f"{и}: ожидался пустой список, получено {sorted(ax)}")
ax4 = классика["delta_all_classical"]
if ax4 is None:
    беды.append("delta_all_classical: не найдено в выводе")
elif ax4 == set():
    беды.append("delta_all_classical: список ПУСТ — найден бесвыборный путь, "
                "это НАХОДКА: правило δ₂ конструктивно, перенести в корпус")
elif ax4 != ЖДЁМ_КЛАССИКУ:
    беды.append(f"delta_all_classical: ярус сменился, получено {sorted(ax4)}")

print("ЯРУС ПРАВИЛ γ/δ — промер, не предсказание")
for и, ax in чистые.items():
    print(f"  {и:28} {'пусто' if ax == set() else sorted(ax)}")
print(f"  {'delta_all_classical':28} {sorted(ax4) if ax4 else 'пусто'}   (вне корпуса)")
print()
if беды:
    print("ЯРУС γ/δ КРАСНО:")
    for б in беды: print("   ", б)
else:
    print("ЯРУС γ/δ ЗЕЛЕНО: три правила на пустом списке, четвёртое классическое, "
          "расхождений 0")
sys.exit(1 if беды else 0)
