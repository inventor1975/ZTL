# -*- coding: utf-8 -*-
"""
ОБРАТНЫЙ ХОД: ОТ РЕЗУЛЬТАТА К МИНИМАЛЬНЫМ НАБОРАМ ВХОДОВ.

Вопрос куратора: после того как тетрадь выдала результат, есть ли смысл
считать обратно — от результата ко входам. Есть, но направление не наше:
обратный ход от вывода к посылкам — это АБДУКЦИЯ, и ей десятки лет. Не наше
и `relevance` из PyArg (Odekerken/Bex/Prakken), которое отвечает «какие
основания ещё способны повлиять».

Промерено 2026-08-30 (`inventory/aspic_relevance*`): их ответ — ПЛОСКОЕ
МНОЖЕСТВО оснований, и оно СОВМЕСТНОСТЬ НЕ НЕСЁТ. Случаи «a И b дают c» и
«a даёт c, b даёт c» дают у них ПОБУКВЕННО один список, а стоят разного:
в первом ни одно основание в одиночку не двигает ничего.

Поэтому здесь считается не список, а СЕМЕЙСТВО МИНИМАЛЬНЫХ НАБОРОВ.

## Два разных вопроса, которые нельзя смешивать

    ВОЗМОЖНОСТЬ  минимальный набор S: СУЩЕСТВУЕТ заполнение S, дающее цель.
                 «что проверить, чтобы цель стала достижима»
    ГАРАНТИЯ     минимальный набор S: ВСЯКОЕ заполнение S даёт цель.
                 «что проверить, чтобы цель наступила КАК БЫ НИ ВЫШЛО»

Смешать их — ровно тот дефект, о котором уже написан пост «вердикт был прав,
а распоряжение — нет»: вердикт верен, а наряд невыполним. Наряд выписывают
по ГАРАНТИИ; ВОЗМОЖНОСТЬ — это только «не безнадёжно».

Минимальность: в семействе нет набора, у которого собственное подмножество
тоже подходит (антицепь).
"""

import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ztl import T, F, Z, ev            # noqa: E402
from ztljudge import judge, _show      # noqa: E402

TERMINAL = {"EARNED", "REFUTED"}


def _disposition(phi, m):
    return judge(_show(phi), m)["disposition"]


def _outcome(phi, m, by_disposition):
    return _disposition(phi, m) if by_disposition else ev(phi, m)


def backward(phi, marking, target, by_disposition=True):
    """От цели назад к минимальным наборам оснований.

    Возвращает dict:
      already      — цель достигнута БЕЗ единой проверки (пустой набор).
      possible     — семейство минимальных наборов: цель СТАНОВИТСЯ достижима.
      guaranteed   — семейство минимальных наборов: цель НАСТУПАЕТ при любом
                     заполнении набора.
      grounds      — какие основания вообще непроверены.

    Пустое семейство означает «такого набора НЕТ», и это сказано полем
    `possible_none` / `guaranteed_none`, а не молчанием: молча пустой список
    читается как «ничего не надо», что противоположно правде.
    """
    grounds = tuple(a for a, v in sorted(marking.items()) if v == Z)
    already = _outcome(phi, marking, by_disposition) == target

    possible, guaranteed = [], []
    for k in range(1, len(grounds) + 1):
        for S in itertools.combinations(grounds, k):
            # минимальность: если собственное подмножество уже в семействе,
            # этот набор не минимален и в ответ не идёт
            sub_p = any(set(prev) < set(S) for prev in possible)
            sub_g = any(set(prev) < set(S) for prev in guaranteed)
            if sub_p and sub_g:
                continue
            hits = []
            for vals in itertools.product((T, F), repeat=k):
                m2 = dict(marking); m2.update(dict(zip(S, vals)))
                hits.append(_outcome(phi, m2, by_disposition) == target)
            if not sub_p and any(hits):
                possible.append(S)
            if not sub_g and all(hits):
                guaranteed.append(S)

    return {"grounds": grounds, "already": already,
            "possible": possible, "guaranteed": guaranteed,
            "possible_none": not possible, "guaranteed_none": not guaranteed,
            "target": target}


def order(phi, marking, target, by_disposition=True):
    """Наряд человеку — по ГАРАНТИИ, не по возможности.

    Наряд, который нельзя исполнить, хуже отказа: см. пост «вердикт был прав,
    а распоряжение — нет». Поэтому возможность здесь НЕ выдаётся за наряд, а
    называется своим именем."""
    r = backward(phi, marking, target, by_disposition)
    if r["already"]:
        return f"проверять нечего: цель {target} уже достигнута"
    if r["guaranteed"]:
        sets = "; ".join("+".join(S) for S in r["guaranteed"])
        return f"проверить ВМЕСТЕ: {sets} — цель {target} наступит в любом случае"
    if r["possible"]:
        sets = "; ".join("+".join(S) for S in r["possible"])
        return (f"ГАРАНТИИ НЕТ. Цель {target} лишь ВОЗМОЖНА, и только если "
                f"проверка ляжет удачно: {sets}")
    return f"НЕТ НАБОРА: цель {target} недостижима никакой проверкой"
