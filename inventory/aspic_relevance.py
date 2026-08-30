# -*- coding: utf-8 -*-
"""
ИХ relevance ПРОТИВ НАШЕЙ ШИРИНЫ — прогоном, не чтением.

Наша ширина: наименьшее число непроверенных оснований, которые надо заполнить
ВМЕСТЕ, чтобы вердикт сдвинулся (`inventory/width/`). Ширина ≥2 значит, что
частичного прогресса нет вообще.

Их `FourBoolRelevanceLister`: какие queryables ещё способны доставить статус.

Два случая: ширина 1 (`a => c`) и ширина 2 (`a, b => c`). Смотрим, различает
ли их вывод СОВМЕСТНОСТЬ — то, что поодиночке основания бесполезны.
Прогноз заморожен в `aspic_relevance_ПРОГНОЗ.md` до запуска.
"""

import sys
from itertools import combinations, product

from py_arg.aspic_classes.literal import Literal
from py_arg.aspic_classes.defeasible_rule import DefeasibleRule
from py_arg.aspic_classes.argumentation_system import ArgumentationSystem
from py_arg.aspic_classes.argumentation_theory import ArgumentationTheory
from py_arg.incomplete_aspic_classes.incomplete_argumentation_theory import (
    IncompleteArgumentationTheory)
from py_arg.algorithms.stability.stability_labeler import StabilityLabeler
from py_arg.algorithms.relevance.relevance_lister import FourBoolRelevanceLister
from py_arg.algorithms.semantics.get_grounded_extension import get_grounded_extension


def build(rules, queryables):
    names = set()
    for _, ants, cons in rules:
        names.update(ants); names.add(cons)
    names.update(queryables)
    names = {n.lstrip("-") for n in names}
    lang = {}
    for n in sorted(names):
        lang[n] = Literal(n); lang["-" + n] = Literal("-" + n)
    contra = {}
    for n in sorted(names):
        contra[n] = {lang["-" + n]}; contra["-" + n] = {lang[n]}
    drules = [DefeasibleRule(rid, {lang[a] for a in ants}, lang[cons])
              for rid, ants, cons in rules]
    system = ArgumentationSystem(lang, contra, [], drules)
    return IncompleteArgumentationTheory(
        argumentation_system=system,
        queryables=[system.language[q] for q in sorted(queryables)],
        knowledge_base_axioms=[], knowledge_base_ordinary_premises=[])


def justified(iat, kb_names, target):
    kb = [iat.argumentation_system.language[n] for n in kb_names]
    at = ArgumentationTheory(iat.argumentation_system, kb, [], None)
    saf = at.create_abstract_argumentation_framework("saf")
    return any(str(a.conclusion) == target
               for a in get_grounded_extension(saf))


def our_width(iat, queryables, target):
    """Наименьшее число оснований, которые надо заполнить ВМЕСТЕ, чтобы
    вердикт стал обоснован хоть при каком-то заполнении."""
    qs = sorted(queryables)
    for k in range(1, len(qs) + 1):
        for subset in combinations(qs, k):
            for vals in product([True, False], repeat=k):
                kb = [(q if v else "-" + q) for q, v in zip(subset, vals)]
                if justified(iat, kb, target):
                    return k, subset, kb
    return None, (), []


def main():
    cases = [
        ("A. ширина 1 — одно основание двигает",
         [("r1", ["a"], "c")], {"a"}),
        ("B. ширина 2 — поодиночке НИЧЕГО не двигает",
         [("r1", ["a", "b"], "c")], {"a", "b"}),
        # РЕШАЮЩИЙ КОНТРОЛЬ. Возразят: «размер списка и есть подсказка, в B
        # он вдвое длиннее». Случай C кроет это возражение: тот же список из
        # четырёх литералов, а ширина 1 — каждое основание достаточно САМО.
        # Если relevance у B и C совпадёт при разной ширине, значит вывод
        # СОВМЕСТНОСТЬ НЕ НЕСЁТ, и дело не в длине.
        ("C. КОНТРОЛЬ: тот же список, но ширина 1 — каждое достаточно само",
         [("r1", ["a"], "c"), ("r2", ["b"], "c")], {"a", "b"}),
    ]
    print("ИХ RELEVANCE ПРОТИВ НАШЕЙ ШИРИНЫ\n")
    out = []
    for title, rules, q in cases:
        iat = build(rules, q)
        labels = StabilityLabeler().label(iat)
        rl = FourBoolRelevanceLister()
        rl.update(iat, labels)
        c = iat.argumentation_system.language["c"]
        rel = sorted(str(x) for x in rl.relevance_list.get(c, set()))
        w, subset, kb = our_width(iat, q, "c")
        # ПРОВЕРКА СОВМЕСТНОСТИ: двигает ли КАЖДОЕ основание в одиночку?
        singles = {qq: any(justified(iat, [qq if v else "-" + qq], "c")
                           for v in (True, False)) for qq in sorted(q)}
        print(f"  {title}")
        print(f"    их relevance для c : {rel}")
        print(f"    наша ширина        : {w}  (набор {list(subset)})")
        print(f"    двигает ли поодиночке: {singles}\n")
        out.append((rel, w, singles))

    print("ИТОГ")
    relA, wA, sA = out[0]
    relB, wB, sB = out[1]
    relC, wC, sC = out[2]
    if relB == relC and wB != wC:
        print(f"  КОНТРОЛЬ ПРОШЁЛ: relevance у B и C ОДИНАКОВ ({relB}),")
        print(f"  а ширина разная — {wB} против {wC}. Значит длина списка")
        print(f"  тут ни при чём: их вывод совместность НЕ НЕСЁТ.\n")
    else:
        print(f"  КОНТРОЛЬ НЕ ПРОШЁЛ: B={relB}/{wB}, C={relC}/{wC}.")
        print(f"  Вывод ниже НЕ опирать на этот прогон.\n")
    if wA != wB and not any(sB.values()):
        print(f"  Наша ширина различает случаи: {wA} против {wB}.")
        print(f"  В случае B ни одно основание в одиночку НЕ двигает: {sB}")
        print(f"  Их relevance в обоих случаях — ПЛОСКОЕ МНОЖЕСТВО литералов")
        print(f"  ({relA} и {relB}); множество не может сказать, что элементы")
        print(f"  нужны ВМЕСТЕ. Совместность из их вывода не читается.")
        print("\n  ЗНАЧИТ: relevance отвечает 'что ещё может повлиять',")
        print("  ширина отвечает 'сколько надо заполнить СРАЗУ'. Разные.")
    else:
        print("  Вывод НЕ подтверждён — разбираться, а не записывать.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
