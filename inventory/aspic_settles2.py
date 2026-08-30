# -*- coding: utf-8 -*-
"""
ВТОРОЙ ЗАХОД: их stability и наш settles — РАЗНЫЕ ВОПРОСЫ. Показываем это
на их же машине, а не рассуждением.

Первый заход дал UNSTABLE в ОБОИХ наших случаях, и это не сбой их алгоритма.
Причина написана в их же исходнике, `incomplete_argumentation_theory.py`,
комментарий к `get_all_axiom_completions` дословно:

    -1: Negation of this queryable is an axiom in the knowledge base.
     0: This queryable remains unknown in that neither this queryable, nor
        its negation is an axiom.
     1: This queryable is an axiom in the knowledge base.

То есть их «будущие теории» ВКЛЮЧАЮТ будущее, где основание так и осталось
непроверенным. Оттого случай «оба исхода проверки дают одно» у них всё равно
нестабилен: есть будущее, где не проверили вовсе.

    ИХ stability:  статус ОДИН во всех будущих, ВКЛЮЧАЯ непроверенное.
                   Вопрос: «может ли дальнейшее дознание что-то изменить».
    НАШ settles:   вердикт ОДИН во всех будущих, где основание ПРОВЕРЕНО.
                   Вопрос: «стоит ли эта проверка чего-нибудь».

Здесь мы считаем НАШ вопрос НА ИХ МАШИНЕ: берём их же перечисление будущих,
выбрасываем незавершённые (value 0) и смотрим, постоянна ли метка.
"""

import sys
from itertools import product

from py_arg.aspic_classes.literal import Literal
from py_arg.aspic_classes.defeasible_rule import DefeasibleRule
from py_arg.aspic_classes.argumentation_system import ArgumentationSystem
from py_arg.aspic_classes.argumentation_theory import ArgumentationTheory
from py_arg.incomplete_aspic_classes.incomplete_argumentation_theory import (
    IncompleteArgumentationTheory)
from py_arg.algorithms.stability.stability_labeler import StabilityLabeler
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
        contra[n] = {lang["-" + n]}
        contra["-" + n] = {lang[n]}
    drules = [DefeasibleRule(rid, {lang[a] for a in ants}, lang[cons])
              for rid, ants, cons in rules]
    system = ArgumentationSystem(lang, contra, [], drules)
    return IncompleteArgumentationTheory(
        argumentation_system=system,
        queryables=[system.language[q] for q in sorted(queryables)],
        knowledge_base_axioms=[], knowledge_base_ordinary_premises=[])


def justified(at, target):
    """Обоснован ли литерал в ЗАВЕРШЁННОЙ теории — по grounded-семантике."""
    saf = at.create_abstract_argumentation_framework("saf")
    grounded = get_grounded_extension(saf)
    return any(str(a.conclusion) == target for a in grounded)


def our_settles(iat, target):
    """НАШ вопрос на их машине: постоянна ли метка по ЗАВЕРШЁННЫМ будущим."""
    pos = iat.positive_queryables
    seen = {}
    for combo in product([-1, 1], repeat=len(pos)):   # 0 ВЫБРОШЕН намеренно
        kb = [iat.argumentation_system.language[
                  ("-" if v == -1 else "") + str(q)]
              for q, v in zip(pos, combo)]
        at = ArgumentationTheory(iat.argumentation_system, kb, [], None)
        seen[combo] = justified(at, target)
    return seen


def main():
    cases = [
        ("1. НЕ РЕШЕНО — правило одно, посылка не проверена",
         [("r1", ["overheat"], "shutdown")], {"overheat"}),
        ("2. РЕШЕНО ЗАРАНЕЕ — оба исхода ведут к одному",
         [("r1", ["overheat"], "shutdown"),
          ("r2", ["-overheat"], "shutdown")], {"overheat"}),
    ]
    print("ИХ ВОПРОС ПРОТИВ НАШЕГО, НА ОДНОЙ И ТОЙ ЖЕ МАШИНЕ\n")
    verdicts = []
    for title, rules, q in cases:
        iat = build(rules, q)
        theirs = StabilityLabeler().label(iat).literal_labeling[
            iat.argumentation_system.language["shutdown"]].stability_str
        ours = our_settles(iat, "shutdown")
        settled = len(set(ours.values())) == 1
        print(f"  {title}")
        print(f"    ИХ stability     : {theirs}")
        print(f"    завершённые будущие: "
              + ", ".join(f"{'/'.join(('+' if v>0 else '-') for v in k)}"
                          f"->{'обоснован' if val else 'нет'}"
                          for k, val in ours.items()))
        print(f"    НАШ settles      : {'РЕШАЕТ' if settled else 'не решает'}\n")
        verdicts.append((theirs, settled))

    print("ИТОГ")
    if verdicts[0][0] == verdicts[1][0] and verdicts[0][1] != verdicts[1][1]:
        print("  Их метка на двух случаях ОДНА, наша РАЗНАЯ.")
        print("  Значит stability и settles — РАЗНЫЕ величины, и разница")
        print("  ровно в том, входит ли в 'будущее' непроверенное основание.")
        print("  Их вопрос: может ли дознание ещё что-то изменить.")
        print("  Наш вопрос: стоит ли эта конкретная проверка чего-нибудь.")
    else:
        print("  Совпало — вывод НЕ подтверждён, разбираться дальше.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
