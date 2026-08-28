# -*- coding: utf-8 -*-
"""Путь наверх для непроверенного — ОПЕРАЦИОННЫЙ, а не социальный.

ВОПРОС, откуда это взялось. Разбирая чужую работу (arXiv 2606.24322), мы
нашли упрёк, который бьёт и по нам: «нет пути, которым законная непроверенная
информация могла бы КОГДА-ЛИБО подействовать». Наши ворота умеют только
отказывать: основание не в реестре — строка не зарабатывает, и попасть в
реестр можно лишь рукой человека. Ворота, умеющие только отказывать, ещё не
механизм управления.

ПОЧЕМУ НЕ ИХ ОТВЕТ. У них подъём СОЦИАЛЬНЫЙ: основание поднимается, когда за
него ручаются двое НЕЗАВИСИМЫХ. «Независимых» — самое хрупкое слово в этой
фразе, и хрупкость его мы промерили сами: `db/probe_containment.py` вводит
МНИМУЮ избыточность — два основания объявлены разными, а происхождение у них
одно, — и меряет, во что это обходится. Взять их подъём значит втащить дефект,
который у себя уже измерен.

НАШ ОТВЕТ. Он уже лежал в ярусах реестра, надо было только увидеть:

    ярус ACT   — основание, которое можно ЗАПУСТИТЬ. Ему не нужно ничьё
                 разрешение; нужно, чтобы оно ОТРАБОТАЛО.
    ярус PLACE — основание, которое можно ОТКРЫТЬ. Тот же ход: не «поверь»,
                 а «посмотри».
    ярус STORY — подняться сам НЕ МОЖЕТ НИКОГДА. Там нет акта, там «так
                 сказано». И это правильно: стипуляция и есть человеческий
                 шаг, автоматической двери у неё быть не должно.

То есть подъём не по СОГЛАСИЮ, а по ВЫПОЛНИМОСТИ — «пошли и посмотрели»,
на чём вся книга и стоит. Диоген не собирал показания, что движение есть.

ЧТО ЭТОТ МОДУЛЬ НЕ ДЕЛАЕТ: не решает, ПРАВ ли акт. Он устанавливает, что акт
СУЩЕСТВУЕТ и ПРОХОДИТ. Основание, чей прогон зелен, допущено к тому, чтобы
зарабатывать; истинность добытого им остаётся вопросом судьи, а не воротам.
"""
from __future__ import annotations
import os
import subprocess

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TIMEOUT = 120


def _inside(ground: str, root: str):
    """Путь ВНУТРИ дерева — или ничего.

    ДЫРА, НАЙДЕННАЯ В СВОЁМ ЖЕ КОДЕ ДО ВЫКАТА (2026-08-28). `performable`
    ЗАПУСКАЕТ то, что названо основанием. Основание приходит из ДОКУМЕНТА,
    а документ может прийти откуда угодно — значит «../../что-нибудь.py»
    заставил бы прибор выполнить чужой файл. Подъём по выполнимости обязан
    быть заперт в дереве проекта, иначе он не путь наверх, а дверь внутрь.

    И отдельно, чтобы никто не узнал этого потом: этот модуль ИСПОЛНЯЕТ
    КОД. Кормить его основаниями из недоверенного документа нельзя ни при
    каких условиях — реестр остаётся тем, что объявляет ХОЗЯИН прогона."""
    путь = os.path.realpath(os.path.join(root, ground))
    корень = os.path.realpath(root)
    return путь if (путь == корень or путь.startswith(корень + os.sep)) else None


def performable(ground: str, root: str = ROOT) -> dict:
    """Существует ли акт, названный основанием, и проходит ли он.

    Основание яруса ACT называет путь к прогону в дереве. Ничего не
    угадываем: не нашли файла — так и говорим, а не считаем «наверное, есть»."""
    путь = _inside(ground, root)
    if путь is None:
        return {"admissible": False, "reason": "ACT_OUTSIDE_TREE",
                "why": f"основание указывает ВНЕ дерева проекта: {ground}"}
    if not (ground.endswith(".py") and os.path.isfile(путь)):
        return {"admissible": False, "reason": "NO_SUCH_ACT",
                "why": f"основание не называет прогон в дереве: {ground}"}
    try:
        p = subprocess.run([os.environ.get("ZTL_PY", "python3"), путь],
                           cwd=root, capture_output=True, timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        return {"admissible": False, "reason": "ACT_TIMED_OUT",
                "why": f"прогон не кончился за {TIMEOUT} с"}
    if p.returncode != 0:
        хвост = (p.stderr or b"").decode("utf-8", "replace").strip().splitlines()
        return {"admissible": False, "reason": "ACT_FAILED",
                "why": (хвост[-1] if хвост else f"код возврата {p.returncode}")}
    return {"admissible": True, "reason": "ACT_PASSED",
            "why": f"прогон {ground} прошёл"}


def locatable(ground: str, needle: str = "", root: str = ROOT) -> dict:
    """Открывается ли названный документ, и есть ли в нём сказанное.

    Ярус PLACE. Без `needle` устанавливается только существование — и это
    ЧЕСТНО НАЗЫВАЕТСЯ: «документ есть, содержимое не сверялось»."""
    путь = _inside(ground, root)
    if путь is None:
        return {"admissible": False, "reason": "PLACE_OUTSIDE_TREE",
                "why": f"основание указывает ВНЕ дерева проекта: {ground}"}
    if not os.path.isfile(путь):
        return {"admissible": False, "reason": "NO_SUCH_PLACE",
                "why": f"документ не открывается: {ground}"}
    if not needle:
        return {"admissible": True, "reason": "PLACE_EXISTS",
                "why": "документ есть; СОДЕРЖИМОЕ НЕ СВЕРЯЛОСЬ"}
    try:
        текст = open(путь, encoding="utf-8", errors="replace").read()
    except OSError as e:
        return {"admissible": False, "reason": "PLACE_UNREADABLE", "why": str(e)}
    if needle in текст:
        return {"admissible": True, "reason": "PLACE_CONFIRMS",
                "why": f"в {ground} найдено искомое"}
    return {"admissible": False, "reason": "PLACE_SILENT",
            "why": f"{ground} открылся, искомого в нём НЕТ"}


def elevate(ground: str, tier: str, needle: str = "", root: str = ROOT) -> dict:
    """Может ли основание войти в реестр САМО, без человека.

    Возвращает и отказ с ПРИЧИНОЙ: «не поднялось» без причины — это то же
    молчание, против которого весь прибор."""
    if tier == "act":
        r = performable(ground, root)
    elif tier == "place":
        r = locatable(ground, needle, root)
    elif tier == "story":
        # НЕТ АВТОМАТИЧЕСКОЙ ДВЕРИ, и это не недоделка, а решение: стипуляция
        # есть человеческий шаг. Поднимать её машиной значило бы стереть
        # различие между «так сказано» и «пошли и посмотрели» — то самое,
        # ради которого весь ярус и заведён.
        r = {"admissible": False, "reason": "STIPULATION_NEEDS_A_PERSON",
             "why": "ярус story не поднимается сам: акта нет, есть только слово"}
    else:
        r = {"admissible": False, "reason": "UNKNOWN_TIER",
             "why": f"ярус {tier!r} не из {{act, place, story, row}}"}
    return {"ground": ground, "tier": tier, **r}
