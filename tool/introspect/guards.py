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
import hashlib
import json
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
    # «save BY virtue of a law» — промах I2 запечатанного прогона; в корпусе таких 4.
    r"\bsave\s+(?:in|where|as|for|by|that|to)\b", r"\bprovided\s+that\b",
    # добавлено по замеру слепых пятен 2026-08-26 (69 единиц корпуса LAW):
    r"\bnotwithstanding\b",           # 33× — сильнейший сторож английского права
    r"\bshall\s+not\s+apply\b", r"\bdoes\s+not\s+apply\b",   # 12× и 3×
    r"\bin\s?so\s?far\s+as\b", r"\bin\s+the\s+event\b",      # 6× и 5×
    r"\bwithout\s+prejudice\b", r"\bexcluding\b",            # 3× и 2×
    r"\bexcept\s+as\b", r"\bbut\s+only\b", r"\bwith\s+the\s+exception\b",
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


_QUOTE_OPEN = "\u2018\u201c\u00ab\"'"


def _is_quoted(text: str, start: int) -> bool:
    """Стоит ли перед находкой открывающая кавычка — то есть ПРИВЕДЕНА ли она.
    Приведённый ограничитель принадлежит ДРУГОМУ документу и нас не связывает."""
    head = (text[max(0, start - 4):start] or "").strip()
    return bool(head) and head[-1] in _QUOTE_OPEN


def document_limits(full_text: str) -> list:
    """Статьи, ограничивающие ВЕСЬ документ. Регулярка, без модели.

    ЦИТИРУЕМЫЕ ограничители ОТБРАСЫВАЮТСЯ. Дефект найден запечатанным прогоном
    (E3, ложный отказ): Хартия ЕС приводит статью 17 ЕКПЧ в пояснительной
    записке, и правило потребовало нести ЧУЖУЮ статью. Логически это «строку
    нашли в документе» принято за «строка относится к утверждению» — наша
    собственная болезнь, поднявшаяся на этаж сторожей."""
    t = full_text or ""
    out = []
    for rx in _DLRX:
        for m in rx.finditer(t):
            if _is_quoted(t, m.start()):
                continue
            out.append(" ".join(m.group(0).split()))
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


# ══ РАЗЪЁМ: документ сам себя объявляет ═════════════════════════════════════
# Замысел куратора 2026-08-26: «законы часто несовершенны, а порой умышленно
# несовершенны — вспомни Уловку-22, там ПЕТЛЯ. Детерминированность на входе
# должны дать САМИ ДОКУМЕНТЫ. Жёстко: разъёмы, подключайтесь; не можете — не
# могу дать вердикт.»
#
# ЧТО ЭТО МЕНЯЕТ, И ПОЧЕМУ ЭТО НЕ КОСМЕТИКА. Всё до сих пор построенное
# улучшало ЧТЕНИЕ. Но если источник кривой НАРОЧНО, чтение — не тот рычаг:
# петлю можно прочесть безупречно и остаться в петле. Единственная честная
# поза — жёсткий разъём и отказ судить, когда он не сошёлся.
#
# ГЛАВНОЕ СЛЕДСТВИЕ: СЛОВАРЬ ТЕРЯЕТ ПРАВО РАЗРЕШАТЬ, СОХРАНЯЯ ПРАВО ЗАПРЕЩАТЬ.
# Раньше молчание словаря значило «сторожа нет, допускай» — это и была дыра.
# Молчание словаря значит «Я НЕ ЗНАЮ». Промерено на запечатанном наборе
# GUARD-SEALED-R1: ложных допусков 4 -> 0, причём НИ ОДНОГО слова в словарь не
# добавлено. Изменилось только право.
#
# АССИМЕТРИЯ, оправдывающая остаток метаязыка здесь: ошибка в словаре разъёма
# даёт МОЛЧАНИЕ (потерю охвата), ошибка в судящем словаре даёт ЛОЖНЫЙ ВЕРДИКТ,
# который поедет дальше как правда. Первое — незнание, второе — ложь.

CLEAR      = "CLEAR"        # документ объявил сторож И утверждение его несёт
BLOCK      = "BLOCK"        # сторож уронен: словарь ВПРАВЕ запрещать
NO_VERDICT = "NO_VERDICT"   # разъём не сошёлся: судить НЕ БЕРЁМСЯ

# Указатель: документ называет сторож ССЫЛКОЙ. По ссылке не надо ПОНИМАТЬ —
# надо ПОЙТИ. Потому указатели переносятся через язык дёшево: одной русской
# фразы хватило там, где судящий словарь потребовал бы русского словаря целиком.
_PTR = [
    r"subject to\s+(?P<t>(?:section|article|clause|paragraph|sub\w*)\s*[\w()\-.]+)",
    r"as defined in\s+(?P<t>(?:section|article|subsection)\s*[\w()\-.]+)",
    r"as stated in\s+(?P<t>(?:clause|article|section)\s*[\w()\-.]+)",
    r"in accordance with\s+(?P<t>(?:section|article)\s*[\w()\-.]+)",
    r"pursuant to\s+(?P<t>(?:section|article)\s*[\w()\-.]+)",
    r"notwithstanding\s+(?P<t>(?:section|article)\s*[\w()\-.]+)",
    r"(?P<t>as aforesaid|as aforementioned)",
    r"в соответствии со\s+(?P<t>статьёй\s*[\w()\-.]+)",
    r"(?P<t>установленных федеральным законом|предусмотренных статьёй\s*[\w()\-.]*)",
]
_PRX = [re.compile(p, re.I) for p in _PTR]


def pointers(text: str) -> set:
    """ЦЕЛИ указателей, объявленных текстом. Сравниваем ЦЕЛЬ, а не наличие:
    утверждение со ССЫЛКОЙ НА ДРУГОЕ не несёт сторож источника."""
    out = set()
    for rx in _PRX:
        for m in rx.finditer(text or ""):
            out.add(" ".join(m.group("t").lower().split()).rstrip(".,;"))
    return out


def conserve_socket(proposition: str, evidence_texts, full_document: str = "",
                    *, citation_scope: str) -> dict:
    """Разъём. Возвращает CLEAR | BLOCK | NO_VERDICT — и НИКОГДА молчаливый проход.

    Порядок НЕ произволен:
      1. словарь ЗАПРЕЩАЕТ — это его право, и оно осталось;
      2. документ объявил сторож указателем и утверждение его НЕ несёт -> BLOCK;
      3. объявил и несёт (ТУ ЖЕ цель) -> CLEAR — единственная дорога к допуску;
      4. не объявил -> NO_VERDICT. Судить не берёмся, и молчим об этом ВСЛУХ.
    """
    base = conserve_with_document(proposition, evidence_texts, full_document,
                                  citation_scope=citation_scope)
    src_p = pointers("\n".join(evidence_texts or []))
    claim_p = pointers(proposition)
    base.update(source_pointers=sorted(src_p), claim_pointers=sorted(claim_p),
                vocab_digest=VOCAB_DIGEST)
    if not base["ok"]:
        return dict(base, verdict=BLOCK)
    if src_p and not (src_p <= claim_p):
        return dict(base, verdict=BLOCK, rule="указатель источника не доехал",
                    disposition="GUARD_NOT_PRESERVED",
                    reason=f"источник ссылается на {sorted(src_p - claim_p)}, "
                           f"утверждение эту ссылку не несёт")
    if src_p:
        return dict(base, verdict=CLEAR, rule="документ объявил и утверждение несёт",
                    reason=f"указатели совпали: {sorted(src_p)}")
    return dict(base, verdict=NO_VERDICT, ok=False,
                rule="разъём не сошёлся", disposition="ABSTAINED_NO_SOCKET",
                reason="документ не объявил свой сторож указателем; молчание "
                       "МОЕГО словаря есть незнание, а не чистота")


# ── ОТПЕЧАТОК СЛОВАРЯ. Дыру нашёл куратор вопросом «это метаязык в коде?»:
# список решает ВСЁ, но в отпечаток расписки не входил — расписки при разных
# словарях были байт в байт одинаковы. Молчаливая подмена была невидима.
VOCAB_DIGEST = hashlib.sha256(
    json.dumps({"markers": _MARKERS, "definitions": _DEF, "doc_limits": _DOC_LIMITS,
                "pointers": _PTR}, ensure_ascii=False, sort_keys=True).encode()
).hexdigest()[:16]
