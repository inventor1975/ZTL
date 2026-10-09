# -*- coding: utf-8 -*-
"""
ОБРАТНЫЙ ХОД: ОТ РЕЗУЛЬТАТА К МИНИМАЛЬНЫМ НАБОРАМ ВХОДОВ.

(Moved from inventory/backward.py into the kernel on 2026-09-24, unchanged,
so the studio can vendor it and show what to check after a verdict.)

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

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from ztl import T, F, Z, ev            # noqa: E402
from ztljudge import judge, _show      # noqa: E402

TERMINAL = frozenset({"EARNED", "REFUTED"})


def _disposition(phi, m):
    return judge(_show(phi), m)["disposition"]


def _outcome(phi, m, by_disposition):
    return _disposition(phi, m) if by_disposition else ev(phi, m)


def _hits(outcome, target):
    """A target is one outcome, or a set of them: TERMINAL asks whether the
    matter is SETTLED either way (added 2026-09-24 for the studio's "what to
    check" — the order that closes the question, whatever the check shows)."""
    return outcome in target if isinstance(target, (set, frozenset)) else outcome == target


# ГДЕ НА САМОМ ДЕЛЕ УХОДИТ ВРЕМЯ — замерено 2026-08-30 на живом случае с
# одиннадцатью основаниями, а не угадано:
#
#     ev    (значение)   0.004 мс
#     grade (гарантия)  424     мс      —  в 97 000 раз дороже
#
# Дело НЕ в числе подмножеств: каждый отдельный расчёт гарантии сам по себе
# перебирает все классические доопределения марок. Отсюда 48 минут там, где
# по значению — доли секунды.
#
# И ЕЩЁ ОДНО, ЧТО ЗАКРЫВАЕТ ОЧЕВИДНЫЙ ОБХОД. Соблазн такой: «раз проверка
# только добавляет знание, вердикт от неё не падает — значит половину можно
# не считать». Для ЛЕНИВОГО регистра это верно и доказано (zarith: сужение
# никогда не отнимает заслуженного). Для ЖАДНОГО, в котором работает судья,
# это ЛОЖЬ, и она промерена: `fixedpoint.py` печатает пять свидетелей
# немонотонности, например {λ=Z} ⊑ {λ=F}, но J(v)={λ=F} ⋢ J(w)={λ=T}.
# Значит сокращать перебор монотонностью здесь НЕЛЬЗЯ.


# ПОТОЛКИ ПРОМЕРЕНЫ, А НЕ НАЗНАЧЕНЫ (2026-08-30). Первый вариант ставил 14
# на глаз; куратор спросил «а сколько НАДО», и вопрос оказался правильным:
# у двух режимов пределы отличаются на порядок.
#
#   оснований   backward по ЗНАЧЕНИЮ   backward по ДИСПОЗИЦИИ
#        8            0.00 с                  1.2 с
#        9            0.01 с                  5.8 с
#       10            0.02 с                 26.8 с
#       12            0.04 с                 (не считается)
#       20            0.57 с                        —
#       24            1.47 с                        —
#
# Причина в `grade`: он сам перебирает доопределения марок и растёт втрое на
# каждое основание (8→10 мс, 10→114 мс, 12→1.2 с, 13→4.1 с), тогда как `ev`
# стоит 0.004 мс и от числа оснований почти не зависит.
#
# Отсюда потолки РАЗНЫЕ, и это честнее одного числа: по значению считать
# можно широко, по диспозиции — только на малом.
CAP_VALUE = 24       # по значению: 1.5 с, дальше просто дорого
CAP_DISPOSITION = 9  # по диспозиции: 5.8 с; на 10 уже 27 с, это не работа
MAX_K = 4            # дальше наборы не ищем, и говорим об этом вслух


def backward(phi, marking, target, by_disposition=True,
             cap_grounds=None, max_k=MAX_K, memo=None, use_tree=True):
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

    ТРИ ЗНАЧЕНИЯ ФЛАГА, НЕ ДВА (2026-09-28, красная команда PR #5):
      True  — искали ВСЁ и не нашли: набора нет;
      False — набор есть (или цель уже достигнута: минимален пустой набор);
      None  — НЕ ИСКАЛИ до конца (поиск обрезан на max_k или отказ на потолке).
    Раньше обрезанный поиск и отказ отвечали True, и order() говорил
    «недостижима никакой проверкой» там, где один g0 = F уже опровергал.
    """
    # READ OFF THE TABLES FIRST (2026-10-09, the curator: "is the backward pass not the
    # forward one read the other way?"). Where every unverified ground occurs once,
    # zbackward_tree builds the same families from the connectives' tables — equal to
    # the enumeration below on 10,500 comparisons (test_backward_tree.py), with no
    # size cut: a conjunction of six grounds, which this function answered "not
    # searched further" past MAX_K = 4, gets its one set of six. Elsewhere (a ground
    # repeated) the enumeration below runs as before.
    if use_tree:
        from zbackward_tree import backward_tree
        got = backward_tree(phi, marking, target, by_disposition)
        if got is not None:
            return got
    grounds = tuple(a for a, v in sorted(marking.items()) if v == Z)
    # ONE OUTCOME PER FILLING (2026-09-27, the cloud's worst-case search, PR #4):
    # the studio asks three targets of the same claim and the same fillings, and
    # each filling is a whole judge. A caller that passes `memo` shares them.
    def outcome(m):
        if memo is None:
            return _outcome(phi, m, by_disposition)
        key = (by_disposition, tuple(sorted(m.items())))
        if key not in memo:
            memo[key] = _outcome(phi, m, by_disposition)
        return memo[key]
    already = _hits(outcome(marking), target)
    # ЦЕЛЬ УЖЕ ДОСТИГНУТА — минимальное семейство {∅}, и больше в нём ничего нет:
    # любой непустой набор содержит ∅ и не минимален. Раньше перебор шёл и тут и
    # выдавал «проверь q» рядом с «уже достигнуто» — и даже атомы, которых в
    # формуле нет (PR #5, B1).
    if already:
        return {"grounds": grounds, "already": True,
                "possible": [], "guaranteed": [],
                "possible_none": False, "guaranteed_none": False,
                "target": target}

    # ПОТОЛОК НАЗВАН, А НЕ ОБНАРУЖЕН ТАЙМАУТОМ (2026-08-30).
    # Первый живой случай — 16 находок ревью OIC, 11 непроверенных оснований —
    # прибор НЕ ДОСЧИТАЛ и был убит по таймауту. Замерено потом: перебор идёт
    # как 3^n вызовов, для 11 оснований это 177147, около минуты; для 15 — уже
    # четверть часа. Молчаливое зависание хуже отказа: отказ виден.
    if cap_grounds is None:
        cap_grounds = CAP_DISPOSITION if by_disposition else CAP_VALUE
    if len(grounds) > cap_grounds:
        return {"grounds": grounds, "already": already,
                "possible": [], "guaranteed": [],
                "possible_none": None, "guaranteed_none": None,
                "target": target,
                "отказ": (f"оснований {len(grounds)}, потолок {cap_grounds} "
                          f"({'по диспозиции' if by_disposition else 'по значению'}): "
                          f"полный перебор здесь идёт как 3^n и не считается. "
                          f"Сузь разметку или подними cap_grounds сознательно.")}

    possible, guaranteed = [], []
    limit = min(len(grounds), max_k)
    for k in range(1, limit + 1):
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
                hits.append(_hits(outcome(m2), target))
            if not sub_p and any(hits):
                possible.append(S)
            if not sub_g and all(hits):
                guaranteed.append(S)

    cut = limit < len(grounds)

    def none(family):
        # пусто при обрезанном поиске — это «не смотрели» (None), а не «нет»
        return False if family else (None if cut else True)

    out = {"grounds": grounds, "already": already,
           "possible": possible, "guaranteed": guaranteed,
           "possible_none": none(possible), "guaranteed_none": none(guaranteed),
           "target": target}
    # ОБРЕЗАННЫЙ ПОИСК ГОВОРИТ, ЧТО ОБРЕЗАН. Пустое семейство при limit < n
    # неотличимо от «наборов нет», а это разные вещи: во втором случае мы
    # знаем, в первом — не смотрели.
    if cut:
        out["не_искал_дальше"] = (
            f"наборы искались до размера {limit} из {len(grounds)} возможных; "
            f"о больших ничего не говорю")
    return out


def order(phi, marking, target, by_disposition=True):
    """Наряд человеку — по ГАРАНТИИ, не по возможности.

    Наряд, который нельзя исполнить, хуже отказа: см. пост «вердикт был прав,
    а распоряжение — нет». Поэтому возможность здесь НЕ выдаётся за наряд, а
    называется своим именем."""
    r = backward(phi, marking, target, by_disposition)
    if r["already"]:
        return f"проверять нечего: цель {target} уже достигнута"
    if "отказ" in r:
        # отказ — не «недостижима»: мы не считали (PR #5, B3)
        return f"НЕ СЧИТАЛ: {r['отказ']}"
    if r["guaranteed"]:
        sets = "; ".join("+".join(S) for S in r["guaranteed"])
        return f"проверить ВМЕСТЕ: {sets} — цель {target} наступит в любом случае"
    if r["guaranteed_none"] is None:
        # до обрезки гарантии не нашлось — но дальше мы не смотрели (PR #5, B2)
        found = ("; ".join("+".join(S) for S in r["possible"])
                 if r["possible"] else "")
        return (f"НЕ ИСКАЛ ДАЛЬШЕ: {r['не_искал_дальше']}. "
                + (f"До этого размера цель {target} лишь ВОЗМОЖНА: {found}"
                   if found else f"До этого размера набора для {target} нет"))
    if r["possible"]:
        sets = "; ".join("+".join(S) for S in r["possible"])
        return (f"ГАРАНТИИ НЕТ. Цель {target} лишь ВОЗМОЖНА, и только если "
                f"проверка ляжет удачно: {sets}")
    return f"НЕТ НАБОРА: цель {target} недостижима никакой проверкой"
