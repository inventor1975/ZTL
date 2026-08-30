# -*- coding: utf-8 -*-
"""
СТАВИМ ПРЕДШЕСТВЕННИКА, А НЕ РАССУЖДАЕМ О НЁМ.

Читая исходник PyArg (Odekerken/Bex/Prakken, пакет python-argumentation),
я увидел в `algorithms/stability/stability_label.py` величину, подозрительно
похожую на наш `settles`: литерал СТАБИЛЕН, если его статус обоснования один
и тот же во всякой будущей теории, получаемой доопределением `queryables`.
Наш `settles` — вердикт не зависит от того, чем заполнится основание.

Читать мало. Прогоняем ТРИ случая и смотрим, что их алгоритм ответит.
Прогноз заморожен в `aspic_settles_ПРОГНОЗ.md` ДО первого запуска.

Запускать интерпретатором venv, где стоит python-argumentation.
"""

import sys

from py_arg.aspic_classes.literal import Literal
from py_arg.aspic_classes.defeasible_rule import DefeasibleRule
from py_arg.aspic_classes.argumentation_system import ArgumentationSystem
from py_arg.incomplete_aspic_classes.incomplete_argumentation_theory import (
    IncompleteArgumentationTheory)
# ВАЖНО: SatisfiabilityLabeler — только ПЕРВЫЙ проход (какие метки ВОЗМОЖНЫ);
# он на обоих наших случаях даёт (U,D,O,B)=все True. Полную величину считает
# StabilityLabeler. Первый прогон я сделал не тем входом и чуть не записал
# «их метрика не различает» — различает, звать надо другое.
from py_arg.algorithms.stability.stability_labeler import StabilityLabeler


def lits(*names):
    return {n: Literal(n) for n in names}


def build(rules, queryable_names, kb=()):
    """rules: [(id, [antecedent_str], consequent_str)]."""
    names = set()
    for _, ants, cons in rules:
        names.update(ants); names.add(cons)
    names.update(queryable_names); names.update(kb)
    names.update("-" + n for n in list(names) if not n.startswith("-"))
    lang = lits(*sorted(names))
    contra = {n: {lang["-" + n]} for n in sorted(names) if not n.startswith("-")}
    contra.update({"-" + n: {lang[n]} for n in sorted(names)
                   if not n.startswith("-")})
    drules = [DefeasibleRule(rid, {lang[a] for a in ants}, lang[cons])
              for rid, ants, cons in rules]
    system = ArgumentationSystem(lang, contra, [], drules)
    return IncompleteArgumentationTheory(
        argumentation_system=system,
        queryables=[system.language[q] for q in sorted(queryable_names)],
        knowledge_base_axioms=[],
        knowledge_base_ordinary_premises=[system.language[k] for k in kb])


def report(title, iat, target):
    labels = StabilityLabeler().label(iat)
    lit = iat.argumentation_system.language[target]
    lab = labels.literal_labeling[lit]
    print(f"  {title}")
    print(f"    {target}: {lab}  ->  {lab.stability_str}")
    return lab.stability_str


def main():
    print("ТРИ СЛУЧАЯ НА ИХ АЛГОРИТМЕ (PyArg, stability)\n")

    # 1. НЕ РЕШЕНО: правило есть, посылку никто не проверял.
    a = build([("r1", ["overheat"], "shutdown")], {"overheat", "-overheat"})
    s1 = report("1. НЕ РЕШЕНО — overheat не проверен", a, "shutdown")

    # 2. РЕШЕНО ЗАРАНЕЕ: оба исхода проверки ведут к одному. Наш settles.
    b = build([("r1", ["overheat"], "shutdown"),
               ("r2", ["-overheat"], "shutdown")], {"overheat", "-overheat"})
    s2 = report("2. РЕШЕНО ЗАРАНЕЕ — оба исхода дают shutdown", b, "shutdown")

    # 3. НЕЧЕГО ЧИТАТЬ: у литерала нет ни правила, ни queryable — аргумент
    # построить не из чего. Сосед нашего E.
    c = build([("r1", ["rain"], "wet")], {"rain", "-rain"})
    s3 = report("3. НЕЧЕГО ЧИТАТЬ — у shutdown нет ни правил, ни посылок",
                c, "-wet")

    print("\nИТОГ")
    print(f"  случай 1 (не решено):     {s1}")
    print(f"  случай 2 (решено заранее): {s2}")
    print(f"  случай 3 (соседний литерал): {s3}")
    if s1 != s2:
        print("\n  ИХ STABILITY РАЗЛИЧАЕТ 1 И 2 — то есть вычисляет ровно то,")
        print("  что мы зовём settles. Заявлять settles своим НЕЛЬЗЯ.")
    else:
        print("\n  1 и 2 совпали. ЭТО НЕ ЗНАЧИТ, ЧТО ИХ ВЕЛИЧИНА СЛАБЕЕ.")
        print("  Причина в их же исходнике: в их 'будущие теории' входит")
        print("  будущее, где основание ТАК И НЕ ПРОВЕРЕНО (значение 0 в")
        print("  get_all_axiom_completions). Разбор — inventory/aspic_settles2.py,")
        print("  где наш вопрос посчитан на их машине.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
