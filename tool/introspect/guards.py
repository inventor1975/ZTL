#!/usr/bin/env python3
"""Сохранение сторожей — два правила, найденные ЗАМЕРОМ, а не рассуждением.

Происхождение (ztl-private/guard-probe/hard/RESULT.md, 2026-08-26): проба на
неявных сторожах дала 4/5, и оба промаха смотрели в РАЗРЕШИТЕЛЬНУЮ сторону —
утверждение выглядело менее обусловленным, чем источник.

  H2  условие внутри ОПРЕДЕЛЁННОГО ТЕРМИНА — судья сказал «ограничения нет»
      там, где оно есть. Ловится правилом 1.
  H4  несколько сторожей, опущен один; частичное сохранение маскирует потерю.
      Ловится правилом 2.

ОБА ПРАВИЛА БЕЗМОДЕЛЬНЫЕ, НО ПО-РАЗНОМУ, и разницу скрывать нельзя:

  ПРАВИЛО 1 — сличение строк. Оговорок нет.
  ПРАВИЛО 2 — счёт маркеров регуляркой. Безмодельно, но ЛОЖНО ОТКАЗЫВАЕТ,
      когда цитируемый кусок широк: в соседних клаузах стоят ЧУЖИЕ маркеры.
      Промерено на контрольной H5 (два `unless`, оба сторожат другое).
      Отсюда УСЛОВИЕ ВКЛЮЧЕНИЯ: правило 2 применимо к УЗКОЙ цитате — одной
      клаузе, не абзацу. Узость задаём мы, она не зависит от модели.

  И ассиметрия шума, которую тоже не спрятать: лишний маркер в ИСТОЧНИКЕ ведёт
  к отказу (безопасно), лишний маркер в КАНДИДАТЕ — к пропуску (опасно).
  Второе есть заявленный предел, а не инвариант.
"""
from __future__ import annotations
import re

Q = r"[\"'‘’“”«»]"          # одиночная кавычка любого вида
QS = rf"(?:{Q}{{1,2}})"                                   # govinfo пишет ''термин''

# ── ПРАВИЛО 1: какие термины ИСТОЧНИК определяет ────────────────────────────
_DEF = [
    rf"the term\s+{QS}(?P<t>[^\"'‘’“”]{{2,60}}?){QS}\s*"
    rf"(?:has the same meaning|means|shall mean|includes)",
    rf"In this (?:law|Law|Act|section|Chapter|Convention)\s*,?\s*"
    rf"{QS}(?P<t>[^\"'‘’“”]{{2,60}}?){QS}",
    rf"{QS}(?P<t>[^\"'‘’“”]{{2,60}}?){QS}\s+means\b",
    rf"(?P<t>[A-Za-z][\w \-]{{2,40}}?)\s+as defined in\b",
]

# ── ПРАВИЛО 2: маркеры сторожа ──────────────────────────────────────────────
# «only», «where», «if» шумны. Шум в ИСТОЧНИКЕ безопасен (лишний отказ),
# в КАНДИДАТЕ опасен. Так и заявлено в шапке.
_MARKERS = [
    r"\bunless\b", r"\bexcept(?:\s+that|\s+where|\s+by|\s+in)?\b",
    r"\bsave\s+(?:in|where|as|for)\b", r"\bprovided\s+that\b",
    r"\bsubject\s+to\b", r"\bto\s+the\s+extent\b", r"\bso\s+long\s+as\b",
    r"\bon\s+condition\b", r"\bconditioned\s+on\b", r"\bonly\b", r"\bsolely\b",
    r"\bin\s+no\s+case\b", r"\bother\s+than\b", r"\bnot\s+contrary\s+to\b",
    r"\bin\s+accordance\s+with\b", r"\bpursuant\s+to\b",
    r"\bas\s+prescribed\s+by\s+law\b", r"\bas\s+determined\s+by\s+law\b",
    r"\bwhere\b", r"\bif\b",
]
_MRX = re.compile("|".join(_MARKERS), re.I)


def defined_terms(text: str) -> set:
    """Термины, которые ИСТОЧНИК определяет. Сличение строк, судья не нужен."""
    out = set()
    for p in _DEF:
        for m in re.finditer(p, text, re.I):
            t = " ".join(m.group("t").split()).strip(" ,;:-—")
            if 2 < len(t) < 60 and not t.lower().startswith(("the purposes",)):
                out.add(t.lower())
    return out


def guard_markers(text: str) -> list:
    """Все вхождения маркеров сторожа. Регулярка, без модели."""
    return [m.group(0).lower() for m in _MRX.finditer(text or "")]


def terms_used(proposition: str, evidence: str) -> set:
    """Определённые источником термины, которые УПОТРЕБЛЯЕТ утверждение."""
    p = " ".join((proposition or "").lower().split())
    return {t for t in defined_terms(evidence) if t in p}


def conserve(proposition: str, evidence_texts, *, citation_scope: str) -> dict:
    """Проверка сохранения сторожей. Возвращает вердикт И своё свидетельство.

    citation_scope ОБЯЗАТЕЛЕН и объявляется ВЫЗЫВАЮЩИМ, а не угадывается здесь:
    цитату выбирает он, ему и объявлять, одна это клауза или кусок.

      'clause' — цитата есть ОДНА клауза. Работают оба правила.
      'wide'   — цитата шире клаузы. Правило 2 неприменимо: чужие маркеры
                 соседей дают ложный отказ, а их отсутствие — ложный пропуск.
                 Тогда ВОЗДЕРЖАНИЕ, а НЕ пропуск.

    Почему широкая цитата не может проходить молча (промерено 2026-08-26,
    все десять векторов проб): при выключенном правиле 2 сквозь широкую цитату
    прошли H1 и H4 — оба с настоящим уроненным сторожем. Выключать проверку и
    пропускать — значит открыть ровно ту дыру, ради которой всё строилось.
    Широкая цитата означает: мы не знаем, КАКАЯ клауза обосновывает утверждение.
    Это незнание, и называть его надо незнанием.

    Цена заявляется: воздержание на чистом утверждении при широкой цитате
    (промерено на контроле H5). Лечится цитированием у́же — а узость цитаты
    в НАШИХ руках, она не от модели зависит.
    """
    if citation_scope not in ("clause", "wide"):
        raise ValueError("citation_scope: 'clause' или 'wide'")
    ev = "\n".join(evidence_texts or [])
    used = terms_used(proposition, ev)
    src_m, cand_m = guard_markers(ev), guard_markers(proposition)
    d = {"defined_terms_used": sorted(used), "citation_scope": citation_scope,
         "source_markers": src_m, "candidate_markers": cand_m}
    # ПРАВИЛО 1 работает при любой ширине цитаты: сличение строк соседей не путает
    if used:
        return dict(d, ok=False, rule="определённый термин",
                    disposition="ABSTAINED_DEFINED_TERM",
                    reason=f"источник определяет термин, употреблённый в "
                           f"утверждении: {sorted(used)}; определение не поднято")
    if citation_scope == "wide":
        return dict(d, ok=False, rule="широкая цитата",
                    disposition="ABSTAINED_WIDE_CITATION",
                    reason="цитата шире клаузы: неизвестно, какая клауза "
                           "обосновывает утверждение; счёт сторожей неприменим")
    if len(src_m) > len(cand_m):
        return dict(d, ok=False, rule="счёт сторожей",
                    disposition="GUARD_NOT_PRESERVED",
                    reason=f"в источнике маркеров {len(src_m)}, в утверждении "
                           f"{len(cand_m)}: сторож не доехал")
    return dict(d, ok=True, rule="", disposition="", reason="")


# ── ПРАВИЛО 3: ОГРАНИЧИТЕЛИ ВСЕГО ДОКУМЕНТА ─────────────────────────────────
# Найдено замером 2026-08-26: сужение цитаты чинит ложные воздержания, но
# ОТКРЫВАЕТ дыру H1 — сторож стоит в ДРУГОЙ статье, и в узкой цитате маркеров
# нет ни у источника, ни у кандидата. Счёт бессилен: считать нечего.
# Такие статьи ограничивают ВЕСЬ документ и потому должны ехать с ЛЮБОЙ
# цитатой из него, где бы клауза ни стояла.
_DOC_LIMITS = [
    r"In the exercise of (?:his|her|their|its) rights and freedoms[^.]{0,400}\.",
    r"These rights and freedoms may in no case[^.]{0,300}\.",
    r"Nothing in this \w+ (?:shall|may) be (?:interpreted|construed)[^.]{0,400}\.",
    r"[Tt]his (?:Chapter|Part|Act|Law|policy|Convention) (?:applies|binds|shall apply)"
    r"(?: only)? to[^.]{0,300}\.",
]
_DLRX = [re.compile(p) for p in _DOC_LIMITS]


def document_limits(full_text: str) -> list:
    """Статьи, ограничивающие ВЕСЬ документ. Регулярка, без модели."""
    out = []
    for rx in _DLRX:
        out += [" ".join(m.group(0).split()) for m in rx.finditer(full_text or "")]
    return out


def _carries(proposition: str, limit: str) -> bool:
    """Несёт ли утверждение этот ограничитель. Грубо: общая знаменательная связка.
    Заявляется как грубая проверка — пересказ ограничителя своими словами она
    НЕ узнает, и это заявленный предел, а не инвариант."""
    p = " ".join((proposition or "").lower().split())
    key = [w for w in limit.lower().split() if len(w) > 5][:6]
    return bool(key) and sum(w in p for w in key) >= max(2, len(key) // 2)


def conserve_with_document(proposition: str, evidence_texts, full_document: str,
                           *, citation_scope: str) -> dict:
    """Оба правила + ограничители всего документа. Порядок НЕ произволен:
    сперва определённый термин (сличение строк), затем ограничители документа
    (они действуют независимо от того, где стоит клауза), затем счёт."""
    lim = document_limits(full_document or "")
    dropped = [l for l in lim if not _carries(proposition, l)]
    base = conserve(proposition, evidence_texts, citation_scope=citation_scope)
    base["document_limits"] = lim
    base["document_limits_dropped"] = dropped
    if base["ok"] and dropped:
        return dict(base, ok=False, rule="ограничитель всего документа",
                    disposition="GUARD_NOT_PRESERVED",
                    reason=f"документ несёт {len(dropped)} ограничител(ь/я) на "
                           f"весь текст, утверждение их не несёт: "
                           f"«{dropped[0][:70]}…»")
    return base
