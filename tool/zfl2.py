# -*- coding: utf-8 -*-
"""
ZFL v2 — one language for the whole instrument, and its surface is a TABLE.

v1 had three input languages and made you declare which one you were in:
`statement` (atoms with statuses and an `assert`), `system` (sentences
defined through each other with `Tr`), and — never exposed in the studio at
all — the sheet language of the numeric floor (`x=1500 earned:inv-17 RUB`).
Two of the three were JSON, all three were hand-written, and the curator's
verdict on them was the only one that mattered: "even I do not understand
how it works."

THE RESHAPE, settled in words before a line was written:

  * the three were never three languages. They are three ROLES of one
    document. `status: "Z"` and `credit` are the same field — the name has
    no witness. `status: "T"` and `earned:inv-17` are the same field, the
    second merely naming the witness. `Tr(x)` is not a genre, it is what a
    name looks like when its ground is a formula over names;

  * so there is ONE document: a list of names, each carrying a ground, plus
    what you claim about them. The GENRE IS COMPUTED, never declared. Which
    instruments run — the passport office, the numeric floor, the ledger,
    the judge — follows from which cells are filled, exactly as this corpus
    computes E, computes the passport, computes the docket's genre. The
    input was the last place still demanding to be told;

  * and the surface is not text. It is a TABLE, the curator's correction to
    a line-based sketch that was still a syntax to learn. A form's columns
    say what goes in them and whether they are required; a grammar does not.
    Formulas survive in exactly two cells, `ground` when a name is defined
    and `claim`, and nowhere else.

THE SPEC BELOW IS THE SINGLE SOURCE. The form's widgets, the validator's
rules, and the reference page are all generated from `COLUMNS` and
`DOC_FIELDS`. A column added here appears in all three or in none — which
is the same anti-drift discipline the rest of this corpus runs on, applied
to the one place a user actually touches.

Localisation is hand-written, EN and RU, and deliberately not machine
translated: this vocabulary IS the content, and an auto-translator turns
"on credit" into "on loan" — precisely the word that carries the meaning.

Run:  python3 tool/test_zfl2.py
"""

# --------------------------------------------------------------- the spec
#
# `type` drives the widget, so the form needs no separate description:
#   choice -> a dropdown        bool   -> a yes/no toggle
#   number -> a stepper         text   -> a field
# `required_when` is a rule the validator reads and the form renders as a
# field that lights up only when it is actually needed.

# THE LANGUAGES, in one place, each written in its own. Adding one is DATA:
# every lookup falls back to English for a string not there yet, so a
# half-translated language works instead of breaking. That fallback is the
# design — it lets a language ship the day somebody needs it rather than the
# day it is finished.
#
# The hand-written rule stands and is why this list is short: this vocabulary
# IS the content, and an automatic translation turns "on credit" into "on
# loan" — precisely the word that carries the meaning.
# (code, what the language calls itself, what to CALL IT TO A MODEL). The
# third field exists because the AI is part of the interface: a studio in
# Hebrew whose assistant answers in English is not localised, it is
# half-localised, and the half that talks is the one people notice.
LANGS = [
    ("en", "English", "English"), ("ru", "Русский", "Russian"),
    ("uk", "Українська", "Ukrainian"), ("he", "עברית", "Hebrew"),
    ("de", "Deutsch", "German"), ("fr", "Français", "French"),
    ("es", "Español", "Spanish"),
]
RTL = {"he"}


COLUMNS = [
    {
        "key": "name", "type": "text", "required": True, "advanced": False,
        "en": ("name", "what we call it; formulas use this"),
        "ru": ("имя", "как называем; им же пользуемся в формулах"),
        "de": ("Name", "wie wir es nennen; damit rechnen auch die Formeln"),
        "fr": ("nom", "comme nous l'appelons ; les formules s'en servent"),
        "es": ("nombre", "cómo lo llamamos; las fórmulas lo usan"),
        "uk": ("ім'я", "як називаємо; ним же користуємось у формулах"),
        "he": ("שם", "איך קוראים לו; באותו שם משתמשים בנוסחאות"),
        "eg": ["line", "budget", "L"],
    },
    {
        "key": "means", "type": "text", "required": False, "advanced": False,
        "en": ("means", "what it MEANS for this to be true"),
        "ru": ("значит", "что означает истинность этого имени"),
        "de": ("bedeutet", "was es HEISST, dass dies wahr ist"),
        "fr": ("signifie", "ce que cela VEUT DIRE que ce soit vrai"),
        "es": ("significa", "qué SIGNIFICA que esto sea verdadero"),
        "uk": ("означає", "що означає істинність цього імені"),
        "he": ("פירושו", "מה זה אומר שהשם הזה אמיתי"),
        "eg": ["the invoice line", "this sentence is false"],
        # not decoration: the gloss is the polarity auditor. `fresh` already
        # means "not revoked", so "not fresh" asserts a positive fact —
        # names lie, glosses do not.
    },
    {
        "key": "status", "type": "choice", "required": True, "advanced": False,
        "options": ["verified", "refuted", "unverified", "defined"],
        # A WIDGET THAT LIED. With no default the cell held "" while the
        # browser, having no matching option, displayed the first one —
        # "verified". So a fresh row SHOWED verified and STORED nothing, and
        # the reader was answering for a status they had never chosen. Found
        # 2026-08-15 by reading the live page rather than the source.
        #
        # The default is the doctrine's own: unverified. Zero trust means a
        # name arrives unearned, the judge already reads an unlisted atom as
        # Z, and a studio whose default was `verified` would be granting
        # truth on credit in its very first row.
        "default": "unverified",
        "en": ("status", "where it stands with us"),
        "ru": ("статус", "откуда оно у нас"),
        "de": ("Status", "woher wir es haben"),
        "fr": ("statut", "d'où cela nous vient"),
        "es": ("estado", "de dónde nos viene"),
        "uk": ("статус", "звідки воно в нас"),
        "he": ("מעמד", "מאיפה זה הגיע אלינו"),
        "labels": {
            "en": {"verified": "verified", "refuted": "refuted",
                   "unverified": "not verified", "defined": "defined"},
            "ru": {"verified": "проверено", "refuted": "опровергнуто",
                   "unverified": "не проверено", "defined": "определено"},
            "de": {"verified": "geprüft", "refuted": "widerlegt", "unverified": "ungeprüft", "defined": "definiert"},
            "fr": {"verified": "vérifié", "refuted": "réfuté", "unverified": "non vérifié", "defined": "défini"},
            "es": {"verified": "verificado", "refuted": "refutado", "unverified": "sin verificar", "defined": "definido"},
            "uk": {"verified": "перевірено", "refuted": "спростовано", "unverified": "не перевірено", "defined": "визначено"},
            "he": {"verified": "מאומת", "refuted": "הופרך", "unverified": "לא אומת", "defined": "מוגדר"},
        },
    },
    {
        # ONE CELL, TWO KINDS OF CONTENT, and the curator was right that this
        # is a trap: `inv-17` is an opaque name the machine never looks
        # inside, `~Tr(L)` is a formula it reads and evaluates. The status
        # decides which — which is coherent, and is exactly the sort of rule
        # a person should not have to hold in their head. So the cell says
        # per row what it wants, and the form asks again whenever the status
        # changes. They are mutually exclusive by construction — a name is
        # witnessed or defined, never both — so two columns would leave one
        # of them always empty; the fix is a cell that announces its mode,
        # not a wider table.
        "key": "ground", "type": "text", "advanced": False,
        "required_when": {"status": ["verified", "refuted", "defined"]},
        "en": ("ground", "what backs it, or the formula defining it"),
        "ru": ("основание", "чем подтверждено или как определено"),
        "de": ("Grundlage", "was es belegt, oder die definierende Formel"),
        "fr": ("fondement", "ce qui l'atteste, ou la formule qui le définit"),
        "es": ("fundamento", "qué lo respalda, o la fórmula que lo define"),
        "uk": ("підстава", "чим підтверджено або як визначено"),
        "he": ("אסמכתא", "מה מאשש אותו, או הנוסחה שמגדירה אותו"),
        "eg": ["inv-17", "~Tr(L)"],
        # THE FIELD OFFERS NAMES INSTEAD OF DEMANDING THEM. Reported live by
        # the curator: a free-text ground made people think the CONTENT
        # mattered. It does not — the machine never looks inside an opaque
        # ground, so the only decision carrying meaning is whether two rows
        # name the SAME ground or different ones. A dropdown of ready-made
        # names leaves exactly that decision and removes the rest, and the
        # commonest refusal in the studio (E_NOGROUND on a row someone
        # marked verified) stops being reachable at all.
        #
        # What is STORED is `ground-1`; what is SHOWN is "Ground 1" or
        # "Основание 1". Two reasons, both load-bearing: the whole cascade
        # rests on ground identity, so switching the interface language must
        # not silently rename anything, and a displayed name with a space in
        # it would be cut in half by E_GROUND_SPACES.
        #
        # `defined` is deliberately absent from `when_status`: there the cell
        # holds a formula the machine reads, not a name it only compares.
        "suggest": {
            "when_status": ["verified", "refuted"],
            "prefix": "ground-",
            "label": {"en": "Ground %d", "ru": "Основание %d"},
            # free text stays reachable, and it is not a courtesy: `inv-17`
            # is the only thing tying a row to a real piece of paper, and a
            # ledger of Ground 1..10 would have thrown that away.
            "own": {"en": "a name of my own…", "ru": "своё имя…"},
        },
        "help_when": {
            "verified": {
                "en": ("the name of the document or act that verified it — "
                       "just a name; the machine never looks inside",
                       "inv-17"),
                "ru": ("имя документа или акта, который это подтвердил — "
                       "просто имя; машина внутрь не смотрит", "inv-17")},
            "refuted": {
                "en": ("the name of what refuted it", "inv-17"),
                "ru": ("имя того, что это опровергло", "inv-17")},
            "defined": {
                "en": ("A FORMULA over other names — this one IS read: "
                       "~Tr(L) says the row is false exactly when L is true",
                       "~Tr(L)"),
                "ru": ("ФОРМУЛА через другие имена — вот её машина читает: "
                       "~Tr(L) значит, что строка ложна ровно когда L "
                       "истинно", "~Tr(L)")},
            "unverified": {
                "en": ("nothing needed — an unverified name has no ground",
                       ""),
                "ru": ("ничего не нужно — у непроверенного имени основания "
                       "нет", "")},
        },
    },
    {
        # WHICH DEPENDENCY THIS IS, which is not the same question as
        # `ground_kind` and must not be folded into it. `ground_kind` says how
        # a ground can be LOST — a document is withdrawn, a certificate
        # expires, an act cannot be taken back. This says what the ground DOES
        # — supports a claim, or permits it. An order and an invoice are both
        # documents and are not interchangeable.
        #
        # Measured, not supposed: db/probe_classes ran a collective at full
        # genuine redundancy in every dimension and losing one agent cost
        # 0.0000 while losing the authority root cost 1.0000. Redundancy in
        # one dimension does not substitute for redundancy in another.
        #
        # ADVANCED and defaulted to evidence, so the table a person fills to
        # count sweets is exactly the table they filled yesterday.
        "key": "dimension", "type": "choice", "required": False,
        "advanced": True, "default": "evidence",
        "options": ["evidence", "authority"],
        "en": ("dimension", "does this SUPPORT the claim or PERMIT it"),
        "ru": ("измерение", "оно ПОДПИРАЕТ утверждение или РАЗРЕШАЕТ его"),
        "de": ("Dimension", "STÜTZT es die Aussage oder ERLAUBT es sie"),
        "fr": ("dimension", "cela SOUTIENT l'affirmation ou l'AUTORISE"),
        "es": ("dimensión", "¿SOSTIENE la afirmación o la PERMITE?"),
        "uk": ("вимір", "воно ПІДПИРАЄ твердження чи ДОЗВОЛЯЄ його"),
        "he": ("ממד", "האם זה תומך בטענה או מתיר אותה"),
        "labels": {
            "en": {"evidence": "evidence (supports)",
                   "authority": "authority (permits)"},
            "ru": {"evidence": "опора (подпирает)",
                   "authority": "разрешение (даёт право)"},
            "de": {"evidence": "Stütze (belegt)", "authority": "Befugnis (erlaubt)"},
            "fr": {"evidence": "appui (soutient)", "authority": "autorité (autorise)"},
            "es": {"evidence": "apoyo (sostiene)", "authority": "autoridad (permite)"},
            "uk": {"evidence": "опора (підпирає)", "authority": "дозвіл (дає право)"},
            "he": {"evidence": "תמיכה (מבססת)", "authority": "סמכות (מתירה)"},
        },
    },
    {
        "key": "ground_kind", "type": "choice", "required": False,
        "advanced": False, "default": "document",
        "options": ["document", "act", "certificate", "row"],
        "en": ("kind of ground", "a document unless you say otherwise"),
        "ru": ("вид основания", "документ, если не сказано иное"),
        "de": ("Art der Grundlage", "ein Dokument, sofern nicht anders gesagt"),
        "fr": ("type de fondement", "un document, sauf mention contraire"),
        "es": ("tipo de fundamento", "un documento, salvo que se diga otra cosa"),
        "uk": ("вид підстави", "документ, якщо не сказано інакше"),
        "he": ("סוג האסמכתא", "מסמך, אלא אם נאמר אחרת"),
        "labels": {
            "en": {"document": "document", "act": "act (nothing to withdraw)",
                   "certificate": "certificate (expires)",
                   "row": "another row"},
            "ru": {"document": "документ", "act": "акт (отзывать нечего)",
                   "certificate": "сертификат (истекает)",
                   "row": "другая строка"},
            "de": {"document": "Dokument", "act": "Handlung (nichts zurückzunehmen)", "certificate": "Zertifikat (läuft ab)", "row": "andere Zeile"},
            "fr": {"document": "document", "act": "acte (rien à retirer)", "certificate": "certificat (expire)", "row": "autre ligne"},
            "es": {"document": "documento", "act": "acto (nada que retirar)", "certificate": "certificado (caduca)", "row": "otra fila"},
            "uk": {"document": "документ", "act": "акт (відкликати нічого)", "certificate": "сертифікат (спливає)", "row": "інший рядок"},
            "he": {"document": "מסמך", "act": "מעשה (אין מה לבטל)", "certificate": "אישור (פג תוקף)", "row": "שורה אחרת"},
        },
    },
    {
        # THE WORLD'S CLOCK, not the inquiry's. Every other column speaks of
        # what is known; this one speaks of what STOPS being true. ZTL has
        # carried the distinction since E25 (`zexpire.py`) and proves it in
        # `EpochBoundary.lean` — two event kinds, `verify` (a mark resolves,
        # we learned) and `expire` (earned ground returns to the mark, the
        # world became different) — but the table had no way to SAY it, so a
        # dilemma whose whole difficulty is temporal (Protagoras v. Euathlus,
        # 2026-08-28) had to be staged by hand in Python. Naming the event
        # here is enough: `expire` sends the value back to the mark, and what
        # it becomes afterwards is a separate act of verification, not
        # something this cell may presume.
        "key": "expires_on", "type": "text", "required": False,
        "advanced": False,
        "en": ("expires at", "the name of the event after which this ground "
               "no longer holds — another row"),
        "ru": ("истекает при", "имя события, после которого это основание "
               "больше не держит — другая строка"),
        "de": ("erlischt bei", "Name des Ereignisses, nach dem diese "
               "Grundlage nicht mehr trägt — eine andere Zeile"),
        "fr": ("expire à", "le nom de l'événement après lequel ce fondement "
               "ne tient plus — une autre ligne"),
        "es": ("expira en", "el nombre del evento tras el cual este "
               "fundamento ya no sostiene — otra fila"),
        "uk": ("спливає при", "ім'я події, після якої ця підстава більше не "
               "тримає — інший рядок"),
        "he": ("פג בעת", "שם האירוע שאחריו האסמכתא כבר אינה מחזיקה — שורה אחרת"),
        "eg": ["court_judgment", "registry_recheck"],
    },
    {
        "key": "value", "type": "text", "required": False, "advanced": False,
        "en": ("value", "a number, an interval [0,10], or ? for unknown"),
        "ru": ("величина", "число, интервал [0,10] или ? для неизвестного"),
        "de": ("Wert", "Zahl, Intervall [0,10] oder ? für unbekannt"),
        "fr": ("valeur", "nombre, intervalle [0,10] ou ? pour inconnu"),
        "es": ("valor", "número, intervalo [0,10] o ? para desconocido"),
        "uk": ("величина", "число, інтервал [0,10] або ? для невідомого"),
        "he": ("ערך", "מספר, תחום [0,10] או ? ללא ידוע"),
        "eg": ["1500", "[0,10]", "?"],
    },
    {
        "key": "unit", "type": "text", "required": False, "advanced": False,
        "en": ("unit", "only with a value; metres never meet roubles"),
        "ru": ("единица", "только с величиной; метры не встречаются с рублями"),
        "de": ("Einheit", "nur mit einem Wert; Meter treffen nie auf Euro"),
        "fr": ("unité", "seulement avec une valeur ; les mètres ne rencontrent pas les euros"),
        "es": ("unidad", "solo con un valor; los metros no se cruzan con los euros"),
        "uk": ("одиниця", "лише з величиною; метри не зустрічаються з гривнями"),
        "he": ("יחידה", "רק עם ערך; מטרים לא נפגשים עם שקלים"),
        "eg": ["RUB", "m", "m2"],
    },
    {
        "key": "scale", "type": "choice", "required": False, "advanced": False,
        "default": "", "options": ["", "int", "decimal2", "frac3"],
        "en": ("scale", "what it rounds to"),
        "ru": ("шкала", "до чего округляем"),
        "de": ("Skala", "worauf gerundet wird"),
        "fr": ("échelle", "jusqu'où l'on arrondit"),
        "es": ("escala", "hasta dónde redondeamos"),
        "uk": ("шкала", "до чого округлюємо"),
        "he": ("סולם", "לאן מעגלים"),
        "labels": {
            "en": {"": "exact", "int": "whole", "decimal2": "hundredths",
                   "frac3": "thirds"},
            "ru": {"": "точно", "int": "целые", "decimal2": "сотые",
                   "frac3": "трети"},
            "de": {"int": "ganze", "decimal2": "Hundertstel", "frac3": "Drittel"},
            "fr": {"int": "entiers", "decimal2": "centièmes", "frac3": "tiers"},
            "es": {"int": "enteros", "decimal2": "centésimas", "frac3": "tercios"},
            "uk": {"int": "цілі", "decimal2": "соті", "frac3": "третини"},
            "he": {"int": "שלמים", "decimal2": "מאיות", "frac3": "שלישים"},
        },
    },
    {
        "key": "sample", "type": "bool", "required": False, "advanced": True,
        "default": False,
        "en": ("separate measurements",
               "each occurrence is its own act of measuring"),
        "ru": ("отдельные измерения",
               "каждое вхождение — свой акт измерения"),
        "de": ("Einzelmessungen", "eine Zahl aus einer Stichprobe, keine einzelne Messung"),
        "fr": ("mesures séparées", "un nombre issu d'un échantillon, pas d'une seule mesure"),
        "es": ("mediciones separadas", "un número de una muestra, no una sola medición"),
        "uk": ("окремі виміри", "число з вибірки, а не одне вимірювання"),
        "he": ("מדידות נפרדות", "מספר מתוך מדגם, לא מדידה אחת"),
    },
]

DOC_FIELDS = [
    {
        # РЕЕСТР ЖИВЁТ В ДОКУМЕНТЕ, а не в параметре вызова — и это разница
        # не удобства, а работоспособности. Ворота оснований существовали с
        # 27.08 и СПАЛИ ВЕЗДЕ: ни книга, ни студия, ни квитанция реестра не
        # подавали (промерено 2026-08-28, `inventory/unwired.py`). Защита,
        # которую надо передать параметром, не передаётся; объявленная В САМОМ
        # ДОКУМЕНТЕ едет с ним через студию, через сохранение и в отпечаток
        # квитанции — потому что она часть того, что документ ГОВОРИТ.
        # Пусто — ворота молчат, и это ВИДНО, а не подразумевается.
        "key": "grounds", "type": "text", "required": False, "advanced": True,
        "en": ("admissible grounds",
               "the grounds this document accepts, comma-separated. A row "
               "earning on a ground outside the list falls to unverified "
               "rather than to false. Empty: the gate says nothing"),
        "ru": ("допустимые основания",
               "основания, которые этот документ признаёт, через запятую. "
               "Строка, заработавшая на основании вне списка, падает в "
               "непроверенное, а не в ложь. Пусто — ворота молчат"),
        "de": ("zulässige Grundlagen",
               "kommagetrennt; leer heißt: das Tor schweigt"),
        "fr": ("fondements admis",
               "separes par des virgules ; vide : la porte se tait"),
        "es": ("fundamentos admitidos",
               "separados por comas; vacio: la puerta calla"),
        "uk": ("допустимі підстави", "через кому; порожньо — ворота мовчать"),
        "he": ("אסמכתאות קבילות", "מופרדות בפסיק; ריק — השער שותק"),
        "eg": ["registry_extract, vehicle_title", "перебор, промер, ch7"],
    },
    {
        "key": "claim", "type": "formula", "required": False,
        "en": ("claim", "what you are actually asserting"),
        "ru": ("утверждение", "что мы, собственно, заявляем"),
        "eg": ["line <= budget", "rain -> umbrella"],
        # optional on purpose: a table of self-referential names with no
        # claim is a perfectly good question — it asks for passports.
    },
    {
        "key": "ask", "type": "multi", "required": False,
        "options": ["verdict", "warranty", "passport", "stipulations",
                    "blast", "brackets"],
        "en": ("ask", "narrow the report; empty shows everything that applies"),
        "ru": ("спросить", "сузить отчёт; пусто — показывается всё применимое"),
    },
]

STATUSES = {c["key"]: c for c in COLUMNS}["status"]["options"]
GROUND_KINDS = {c["key"]: c for c in COLUMNS}["ground_kind"]["options"]


def column(key):
    for c in COLUMNS:
        if c["key"] == key:
            return c
    return None


def form_spec(lang="en"):
    """Everything the UI needs to draw the table, and nothing it has to
    invent: label, help, widget, options with their labels, whether the
    cell is required and under what condition."""
    def render(c):
        label, help_ = c.get(lang, c["en"])
        out = {"key": c["key"], "label": label, "help": help_,
               "help_when": {k: {"help": v.get(lang, v["en"])[0],
                                 "eg": v.get(lang, v["en"])[1]}
                             for k, v in (c.get("help_when") or {}).items()},
               "widget": c["type"], "advanced": c.get("advanced", False),
               "required": c.get("required", False),
               "required_when": c.get("required_when"),
               "default": c.get("default"), "eg": c.get("eg", [])}
        if c["type"] in ("choice", "multi"):
            labels = c.get("labels", {}).get(lang, {})
            out["options"] = [{"value": o, "label": labels.get(o, o)}
                              for o in c["options"]]
        s = c.get("suggest")
        if s:
            out["suggest"] = {"when_status": s["when_status"],
                              "prefix": s["prefix"],
                              "label": s["label"].get(lang, s["label"]["en"]),
                              "own": s["own"].get(lang, s["own"]["en"])}
        return out
    return {"columns": [render(c) for c in COLUMNS],
            "document": [render(c) for c in DOC_FIELDS],
            "langs": [{"code": c, "label": n} for c, n, _e in LANGS],
            "rtl": lang in RTL}


# ------------------------------------------------------- validation
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ztljudge import judge, formalize                            # noqa: E402
from znumjudge import parse_quantities, judge_sheet_claim        # noqa: E402
from znumsolve import solve_claim                                # noqa: E402
import zpassport                                                 # noqa: E402
import zbook                                                     # noqa: E402

NAME_RE = re.compile(r"^[A-Za-zА-Яа-яЁё_][\w А-Яа-яЁё-]*$")

# status -> what the core's two floors each call it
_MARK = {"verified": "T", "refuted": "F", "unverified": "Z"}
_PROV = {"verified": "earned", "refuted": "earned", "unverified": "credit"}
# kind of ground -> the prefix the ledger reads
_KIND_PREFIX = {"document": "", "act": "performed/",
                "certificate": "expiring/", "row": "claim/"}


def _issue(level, code, where, hint):
    return {"level": level, "code": code, "where": where, "hint": hint}


def coerce(doc):
    """A document arriving as JSON has JSON's types, not ours: a model that
    writes `"value": 3000` is not wrong, and neither is a caller who does.
    Everything below reads cells as text, so cells become text here — once,
    at the door, rather than defensively in twenty places.

    Found the moment the AI first filled the table (AttributeError: 'int'
    object has no attribute 'strip'), which is the argument for letting it
    try rather than only testing by hand."""
    if not isinstance(doc, dict):
        return {"rows": [], "claim": ""}
    # `grounds` проходит ЗДЕСЬ, иначе поле уровня документа теряется в
    # дверях: coerce строит новый словарь, и всё, что не перечислено, не
    # доезжает. Ровно так первая редакция реестра-в-документе молча ничего
    # не делала (промерено 2026-08-28).
    out = {"claim": str(doc.get("claim") or ""),
           "grounds": str(doc.get("grounds") or ""),
           "ask": doc.get("ask") or [], "rows": []}
    for r in (doc.get("rows") or []):
        if not isinstance(r, dict):
            continue
        row = {}
        for k, v in r.items():
            if k == "sample":
                row[k] = bool(v)
            elif v is None:
                row[k] = ""
            elif isinstance(v, bool):
                row[k] = v
            else:
                row[k] = str(v)
        out["rows"].append(row)
    return out


def validate(doc):
    """Machine-readable issues, addressed to a CELL. The repair loop and the
    form's inline errors read the same list — `where` is `row 2 / ground`
    rather than a path into a JSON tree, because the person fixing it is
    looking at a table."""
    doc = coerce(doc)
    issues, rows = [], doc["rows"]
    if not rows:
        issues.append(_issue("error", "E_EMPTY", "table",
                             "the table has no rows"))
    seen = set()
    for i, r in enumerate(rows, 1):
        at = f"row {i}"
        name = (r.get("name") or "").strip()
        if not name:
            issues.append(_issue("error", "E_NONAME", f"{at} / name",
                                 "every row needs a name"))
        elif not NAME_RE.match(name):
            issues.append(_issue("error", "E_BADNAME", f"{at} / name",
                                 f"'{name}' is not usable in a formula"))
        elif name in seen:
            issues.append(_issue("error", "E_DUPNAME", f"{at} / name",
                                 f"'{name}' is already used above"))
        seen.add(name)

        status = (r.get("status") or "").strip()
        if status not in STATUSES:
            issues.append(_issue("error", "E_STATUS", f"{at} / status",
                                 f"status must be one of {STATUSES}"))

        # SCALE — сверять с допустимым, а не глотать молча. Поле объявлено
        # выбором, но decimalK/fracM параметрические, потому проверяем ФОРМАТ и
        # границу. Аудит 2026-08-25 показал: без этой проверки decimal5000000
        # доходил до 10**k и вешал сервер; DoS уже закрыт потолком в znumjudge,
        # здесь — чтобы кривой scale ПОМЕЧАЛСЯ, а не тихо игнорировался.
        scale = (r.get("scale") or "").strip()
        if scale and scale not in ("int",):
            import re as _re
            m = _re.fullmatch(r"(decimal(\d+)|frac(\d+))", scale)
            bad_scale = True
            if not m:
                issues.append(_issue("error", "E_SCALE", f"{at} / scale",
                    "scale must be empty, int, decimalK or fracM"))
            elif m.group(2) is not None and int(m.group(2)) > 30:
                issues.append(_issue("error", "E_SCALE", f"{at} / scale",
                    f"decimal places capped at 30 (got {m.group(2)})"))
            elif m.group(3) is not None and (int(m.group(3)) < 1 or int(m.group(3)) > 10**9):
                issues.append(_issue("error", "E_SCALE", f"{at} / scale",
                    "frac denominator must be between 1 and 1e9"))
            else:
                bad_scale = False        # scale ЗАКОННЫЙ — проверять строку дальше
            # ПРЫГАЕМ ТОЛЬКО ЧЕРЕЗ СЛОМАННЫЙ scale, а не через всякий.
            # Дыра, промеренная 2026-08-27: `continue` стоял на уровне всей
            # ветки, поэтому строка с ЗАКОННЫМ `decimal2` пропускала остаток
            # проверок — и `verified` БЕЗ ОСНОВАНИЯ проходил чисто. То есть
            # одна необязательная клетка отключала центральное правило языка.
            if bad_scale:
                continue
        # ONLY GROUND CAN EXPIRE — the same precondition `zexpire.expire`
        # asserts. A mark has nothing to lose, and a sentence is not held by
        # a clock; declaring either as expiring would let the report stage a
        # crossing that the event layer refuses to take.
        exp = (r.get("expires_on") or "").strip()
        if exp and status not in ("verified", "refuted"):
            # The quoting here is deliberately dull: a nested same-quote
            # f-string parses on 3.12 and is a SyntaxError on the 3.11 that
            # CI runs, and a local `ast.parse` will not tell you (measured
            # 2026-08-28 — the stand went red on push, not here).
            shown = status or "empty"
            issues.append(_issue(
                "error", "E_EXPIRY_NO_GROUND", f"{at} / expires_on",
                "only earned ground can expire: this row is "
                f"'{shown}', and there is nothing for the clock "
                "to take back"))
        ground = (r.get("ground") or "").strip()
        if status in ("verified", "refuted", "defined") and not ground:
            # NAMES THE EXIT, not just the rule. Reported live: two atoms
            # marked verified for a toy `rain -> umbrella` produced two
            # refusals and no way forward — the message stated the law and
            # left the reader to guess the move. Both moves are legitimate,
            # and the second one is the doctrine rather than a loophole: a
            # supposition IS a ground once it is named, because then it is
            # visible and can be withdrawn. What the machine refuses is an
            # ANONYMOUS stipulation, never a declared one.
            issues.append(_issue("error", "E_NOGROUND", f"{at} / ground",
                                 "'verified', 'refuted' and 'defined' need a "
                                 "ground. Either name what backs it — a "
                                 "supposition counts once it is named, e.g. "
                                 "by-assumption — or set the status to "
                                 "'not verified'"))
        # A GROUND IS AN IDENTIFIER. The sheet is space-separated, so a
        # ground with a space is silently CUT — and a ground's whole job is
        # identity, which makes a truncated one a different document that
        # happens to look right. Seen live: "утверждение пользователя"
        # became the ground "утверждение".
        if status in ("verified", "refuted") and re.search(r"[\s,]", ground):
            issues.append(_issue(
                "error", "E_GROUND_SPACES", f"{at} / ground",
                "a ground is one word — it names a document, and a space "
                "would cut the name in half: write the-story or inv-17"))
        dim = (r.get("dimension") or "evidence").strip()
        if dim not in ("evidence", "authority"):
            issues.append(_issue("error", "E_DIM", f"{at} / dimension",
                                 "dimension must be evidence or authority"))
        kind = (r.get("ground_kind") or "document").strip()
        if dim == "authority" and kind not in ("document", ""):
            issues.append(_issue(
                "error", "E_DIM_CLASH", f"{at} / dimension",
                "a ground carries one mark, not two: 'authority' cannot be "
                "combined with an act, a certificate or another row. Say "
                "which one matters more and use that"))
        if kind not in GROUND_KINDS:
            issues.append(_issue("error", "E_KIND", f"{at} / kind of ground",
                                 f"kind must be one of {GROUND_KINDS}"))
        if status == "defined":
            try:
                _formula_prop(ground)
            except Exception as exc:
                issues.append(_issue("error", "E_FORMULA",
                                     f"{at} / ground", str(exc)))
        # THE SHAPE OF A VALUE, answered at the cell rather than by a parse
        # error. `(0,10)` and `{0,10}` are the two a person reaches for
        # next after `[0,10]`, and the floor accepts neither — but
        # "cannot parse sheet entry: 'x=(0'" is not an answer to anybody.
        val = (r.get("value") or "").strip()
        if val:
            if re.match(r"^[(\[]\s*[-\d.]+\s*,\s*[-\d.]+\s*[)\]]$", val) \
                    and not re.match(r"^\[[^,]+,[^,]+\]$", val):
                issues.append(_issue(
                    "error", "E_OPEN_INTERVAL", f"{at} / value",
                    "an open bound is not part of a value here: write the "
                    "closed interval [0,10], or put the strictness in the "
                    "claim — `x > 0 & x < 10`"))
            elif val.startswith("{"):
                issues.append(_issue(
                    "error", "E_VALUE_SET", f"{at} / value",
                    "a choice between separate values is not a quantity: "
                    "give each its own row, or write the interval that "
                    "covers them"))
            elif not re.match(r"^(\?|\[[^\]]+\]|[-\d][\d.,/eE+-]*)$", val):
                issues.append(_issue(
                    "error", "E_VALUE_FORM", f"{at} / value",
                    "a value is a number, an interval [0,10], or ? — "
                    f"'{val}' is none of them"))
        # an unreadable unit is an answer at the cell, not an exception
        # thrown from three modules down
        unit = (r.get("unit") or "").strip()
        if unit:
            try:
                import znum
                znum._unit_map(unit)
            except Exception:
                issues.append(_issue(
                    "error", "E_UNIT", f"{at} / unit",
                    f"'{unit}' cannot be read as a unit: a word, optionally "
                    f"with a power (m2), joined by · or /"))
        if r.get("unit") and not (r.get("value") or "").strip():
            issues.append(_issue("warn", "W_UNIT_NO_VALUE",
                                 f"{at} / unit",
                                 "a unit with no value says nothing"))
        if not (r.get("means") or "").strip():
            issues.append(_issue("warn", "W_NO_GLOSS", f"{at} / means",
                                 "without a gloss nobody can check that the "
                                 "name means what it seems to"))
    declared = {(r.get("name") or "").strip() for r in rows}
    for i, r in enumerate(rows, 1):
        # The table is a closed world for events too: an event nobody
        # declared cannot be staged, and a silent unknown here would print a
        # crossing that never happens.
        ev = (r.get("expires_on") or "").strip()
        if ev and ev not in declared:
            issues.append(_issue(
                "error", "E_UNKNOWN_NAME", f"row {i} / expires_on",
                f"no row is called ['{ev}'] — an event is a row like any "
                f"other name"))
    for i, r in enumerate(rows, 1):
        if (r.get("status") or "") == "defined":
            unknown = names_in(r.get("ground")) - declared
            if unknown:
                issues.append(_issue(
                    "error", "E_UNKNOWN_NAME", f"row {i} / ground",
                    f"no row is called {sorted(unknown)}"))
    claim = normalise((doc.get("claim") or "").strip(), rows)
    if claim:
        try:
            _formula(claim, {r.get("name"): r for r in rows})
        except Exception as exc:
            issues.append(_issue("error", "E_CLAIM", "claim", str(exc)))
        unknown = names_in(claim) - declared
        if unknown:
            issues.append(_issue("error", "E_UNKNOWN_NAME", "claim",
                                 f"no row is called {sorted(unknown)}"))
    return issues


def names_in(text):
    """Every name a formula mentions. A table is a closed world: a formula
    may only speak of rows that exist, and a typo in a name is the commonest
    way to ask a question about nothing at all."""
    t = re.sub(r"\bTr\s*\(\s*([^)]+?)\s*\)", r"\1", text or "")
    words = set(re.findall(r"[A-Za-zА-Яа-яЁё_][\wА-Яа-яЁё]*", t))
    return {w for w in words
            if w not in {"not", "and", "or", "imp", "xor", "xnor", "T", "F",
                         "Z", "sum", "min", "max", "abs"}}


_LONE_EQ = re.compile(r"(?<![<>=!])=(?!=)")


# The connectives people (and models) actually type. `and` is not a second
# operator, it is the same one spelled out — refusing it teaches nobody
# anything and costs an answer. Found when the model wrote
# "M = start - toV - give and P = give" and the arithmetic reader choked.
_WORDS = [(r"\band\b", "&"), (r"\bи\b", "&"),
          (r"\bor\b", "|"), (r"\bили\b", "|"),
          (r"\bnot\b", "~"), (r"\bне\b", "~"),
          (r"\bimplies\b", "->")]


def normalise(claim, rows):
    """`x - 10 = 20` is what a person writes, and it is not wrong.

    A single `=` is the biconditional in the propositional parser and
    equality in the numeric one, which is fine as long as nobody has to
    know that. Where the document has quantities, a lone `=` is read as
    equality — the reading anyone typing an equation intends. Elsewhere it
    keeps its propositional sense."""
    out = claim or ""
    for pat, sym in _WORDS:
        out = re.sub(pat, sym, out)
    if numeric_rows(rows) and _LONE_EQ.search(out):
        out = _LONE_EQ.sub("==", out)
    return out


def _formula_prop(text):
    """A DEFINED row's ground is always propositional, so `=` there is the
    biconditional and never a numeric comparison. Reading it as a comparison
    is how converting the docket's own examples first crashed the fixed
    point with KeyError('comparison')."""
    t = re.sub(r"\bTr\s*\(\s*([^)]+?)\s*\)", r"\1", text or "")
    for pat, sym in _WORDS:
        t = re.sub(pat, sym, t)
    return formalize(t)


def _formula(text, _names):
    """One infix syntax for the whole language: `~a & b -> c`, `Tr(L)`, and
    comparisons `x <= y` where the numeric floor takes over. Tr() is folded
    to a bare reference here — self-reference is a property of the GROUND
    being a formula over names, not a separate operator the reader has to
    know."""
    t = re.sub(r"\bTr\s*\(\s*([^)]+?)\s*\)", r"\1", text)
    for pat, sym in _WORDS:
        t = re.sub(pat, sym, t)
    if re.search(r"(<=|>=|==|<|>)", t):
        return ("comparison", t)          # the sheet judge parses these
    return formalize(t)


# ------------------------------------------------- the table, into the core
#
# Nothing here decides WHICH question is being asked. Each converter simply
# reports whether it has anything to say about this table, and `run` calls
# the ones that do. That is what "the genre is computed" means in code.

def _witness(row):
    kind = (row.get("ground_kind") or "document").strip() or "document"
    # One prefix per ground, never two — the ledger accepts `authority/x` or
    # `expiring/x` and not `authority/expiring/x`. The clash is refused in
    # `validate` with the reason, rather than silently resolved here in favour
    # of whichever branch happens to run first.
    if (row.get("dimension") or "evidence").strip() == "authority":
        return "authority/" + (row.get("ground") or "").strip()
    return _KIND_PREFIX.get(kind, "") + (row.get("ground") or "").strip()


def numeric_rows(rows):
    return [r for r in rows if (r.get("value") or "").strip()]


def to_sheet(rows):
    """The numeric floor's own line, assembled from the cells so that nobody
    has to write it. `x=1500 earned:inv-17 RUB` was always a good language —
    it was just never a language anyone should have to TYPE."""
    parts = []
    for r in numeric_rows(rows):
        prov = (f"earned:{_witness(r)}"
                if (r.get("status") == "verified" and r.get("ground"))
                else "credit")
        bits = [f"{r['name']}={r['value'].strip()}", prov]
        if (r.get("scale") or "").strip():
            bits.append(r["scale"].strip())
        if (r.get("unit") or "").strip():
            bits.append(r["unit"].strip())
        if r.get("sample"):
            bits.append("sample")
        parts.append(" ".join(bits))
    return ", ".join(parts)


def to_marking(rows):
    """Statuses as the propositional judge reads them. A `defined` row is
    not a marking entry — it is a sentence, and belongs to the system."""
    return {r["name"]: _MARK[r["status"]] for r in rows
            if r.get("status") in _MARK and not (r.get("value") or "").strip()}


def to_system(rows):
    """The self-referential part, if there is one. Names a definition leans
    on that are NOT themselves defined enter as inputs carrying their own
    status — an unverified input imported into the system, exactly as v1
    did it, but without anyone having to declare a genre to get there."""
    defined = {r["name"]: r for r in rows if r.get("status") == "defined"}
    if not defined:
        return {}
    system = {}
    for name, r in defined.items():
        system[name] = _formula_prop(r.get("ground") or "")
    for r in rows:
        if r["name"] in defined:
            continue
        if any(r["name"] in names_in(d.get("ground") or "")
               for d in defined.values()):
            system[r["name"]] = _MARK.get(r.get("status"), "Z")
    return system


def to_book(rows):
    """The ledger's view: one claim per row that has a value, grounded as the
    row says. This is what makes blast radius and trust brackets reachable
    from the same table."""
    book = []
    for r in numeric_rows(rows):
        # a `?` is a QUESTION, not a claim about a value: there is nothing
        # for the ledger to hold, and building `b == ?` crashed the sheet
        # parser outright (found by running every catalogue example, which
        # is the whole reason they are run rather than merely stored)
        if (r.get("value") or "").strip() == "?":
            continue
        prov = (f"earned:{_witness(r)}"
                if (r.get("status") == "verified" and r.get("ground"))
                else "credit")
        book.append((r["name"], f"{r['name']} == {r['value'].strip()}",
                     f"{r['name']}={r['value'].strip()} {prov}"))
    return book


def applies(doc):
    """Which instruments have something to say. The report shows these and
    no more; nobody chooses a tab."""
    rows = doc.get("rows") or []
    return {
        "numeric": bool(numeric_rows(rows)),
        "passport": bool(to_system(rows)),
        # THE LEDGER APPLIES WHENEVER THERE ARE GROUNDS AT ALL, not only
        # when an exotic kind is chosen. The curator, looking at the form:
        # "ground is unclear and answers for nothing — remove it and use
        # `means` instead and nothing changes." Half right, and the half
        # that was right was ours: the name carries IDENTITY, so two rows
        # on one document fall together and the blast radius is computed
        # from it — but none of that was on screen unless you happened to
        # pick a certificate. A column whose work is invisible is a column
        # that does nothing, whatever the code knows.
        "ledger": bool(to_book(rows)) and any(
            (r.get("ground") or "").strip() for r in numeric_rows(rows)),
        # THE EPOCH FLOOR speaks whenever a row declares a clock. It needs a
        # claim too: what it measures is whether the CONCLUSION survives the
        # world changing, which is `EpochBoundary.epoch_boundary_iff` read
        # over one document instead of over every formula at once.
        "epoch": bool((doc.get("claim") or "").strip()) and any(
            (r.get("expires_on") or "").strip() for r in rows),
        "judge": bool((doc.get("claim") or "").strip()),
    }


def missing_facts(claim, sheet, unknowns, limit=4):
    """How many more FACTS the question needs, found by trying.

    "I have 2 more than Petya and 3 less than Vasya — how much do I have?"
    has no answer: two relations, three unknowns. The solver says OPEN and
    lists six cures, `measure me · measure petya · measure vasya · …`, which
    is true and reads as though all of them were needed. One would do.

    Rather than reason about the rank of a system, this MEASURES it the way
    everything else here is measured: pin one unknown at a trial value,
    re-solve, and see what follows. If the rest fall into place, the
    question was one fact short, and the report can say so and name the
    choices. That is a different sentence from "measure everything", and it
    is the one the person asked for."""
    if not unknowns:
        return None
    enough = []
    for name in unknowns:
        parts = []
        for piece in sheet.split(", "):
            n = piece.split("=", 1)[0].strip()
            parts.append(f"{n}=7 credit" if n == name else piece)
        try:
            q2, m2 = parse_quantities(", ".join(parts))
            r2 = solve_claim(claim, q2, m2)
        except Exception:
            continue
        pinned = {k for k, v in (r2.get("solved") or {}).items()
                  if v.get("pinned")}
        if len(pinned | {name}) >= len(unknowns):
            enough.append(name)
        if len(enough) >= limit:
            break
    if enough:
        return {"needs": 1, "any_of": enough}
    return {"needs": None, "any_of": []}


# ЯРУСЫ, КОТОРЫЕ НИКТО НЕ МОЖЕТ ПРОВЕРИТЬ ДЕЙСТВИЕМ ИЛИ ОТКРЫВ ДОКУМЕНТ.
# Основание яруса `act` можно ЗАПУСТИТЬ, яруса `place` — ОТКРЫТЬ. А `story`
# держится на том, что так СКАЗАНО внутри разобранного случая. Это третий рог
# Агриппы, и наша же книга (гл. 13) говорит, что делать: «стена перестаёт быть
# позором, когда на ней висит табличка», судья метит такое основание как
# решаемое ВЫБОРОМ, а всё, что на нём стоит, получает бирку с именем виновника.
# До 2026-08-28 бирки не было: строка на назначенном зарабатывала МОЛЧА,
# наравне с той, под которой лежит прогон.
СТИПУЛЯЦИЯ = {"story"}


def on_stipulation(rows, registry):
    """Имена, заработавшие на ОБЪЯВЛЕННОМ, а не на предъявимом.

    Работает, только если реестр пришёл С ЯРУСАМИ (словарём). Плоское
    множество ярусов не несёт — тогда молчим, а не догадываемся: назвать
    стипуляцией то, про что нам не сказали, было бы ровно тем сортом
    домысла, против которого весь прибор."""
    if not isinstance(registry, dict):
        return []
    вина = []
    for r in rows:
        if r.get("status") not in ("verified", "refuted"):
            continue
        ярус = registry.get((r.get("ground") or "").strip())
        if ярус in СТИПУЛЯЦИЯ:
            вина.append({"name": r["name"], "ground": r.get("ground"),
                         "tier": ярус})
    return вина


def demote_unregistered(rows, registry):
    """Ворота оснований — слово куратора 2026-08-27 («почини»).

    Дыра, промеренная в тот же день: у `verified` основание проверяется на
    ФОРМУ (непустое, без пробелов) и никогда — на существование; строка с
    основанием `ОСНОВАНИЕ-КОТОРОГО-НЕТ` зарабатывала `T EARNED hereditary`.
    В книге `по-построению` стояло основанием заработанного 8 раз.

    Лекарство НЕ сертификат и НЕ внешний потребитель (куратор насторожился — и прав):
    просто необязательный СПИСОК допустимых оснований. Дал список — слово не
    из списка НЕ зарабатывает: строка судится как `unverified`, то есть
    падает в кредит, а не в ложь. Не дал — поведение прежнее, байт в байт.
    Fail-closed в духе ядра: непредъявленное основание не покупает вердикт."""
    out, demoted = [], []
    for r in rows:
        g = (r.get("ground") or "").strip()
        if r.get("status") in ("verified", "refuted") and g not in registry:
            r2 = dict(r)
            r2["status"], r2["ground"] = "unverified", ""
            out.append(r2)
            demoted.append(r["name"])
        else:
            out.append(r)
    return out, demoted


def resolved_marking(rows):
    """The marking the judge should have seen all along.

    `to_marking` reports the marks and stops, because a `defined` row is a
    sentence rather than a mark. True — and it leaves the judge blind to
    every value the sentences DETERMINE: a claim over defined names came
    back `Z` however well grounded its parts were. The passport already
    computes those values (the least fixed point of the lazy jump), so here
    they are simply added on top of the marks. The marks win where both
    speak: a row that was checked is not overruled by a computation."""
    m = dict(to_marking(rows))
    system = to_system(rows)
    if system:
        lfp, _, _ = zpassport.passports(system)
        for name, v in lfp.items():
            m.setdefault(name, v)
    return m


def unredeemable(comp_kind):
    """Names whose mark no act can ever lift.

    THE SEAM THIS CLOSES (2026-08-28, found by marking up Protagoras v.
    Euathlus). The judge and the passport read the same document and never
    exchanged a word: `to_marking` drops `defined` rows on purpose — a
    sentence is not a mark — so the judge saw an unmarked atom, said
    `until-verification` and sent the reader off to check the liar, while
    the passport in the SAME report said the refusal was permanent.

    The grade was not miscomputed; it was computed over a marking that
    could not say what the sentences forbid. `ZTime.Completable` names the
    missing notion and `ZTime.flip_only_where_forbidden` proves the shape
    of the lie: the flip `until` promises can only happen at an ending the
    system itself rules out. Here that theorem's hypothesis is read off
    the passport, which has always known it — a PARADOX component, and
    whatever hangs off one."""
    out = set()
    for name, (kind, param) in comp_kind.items():
        if kind == "PARADOX" or (kind == "DOWNSTREAM" and param == "permanent"):
            out.add(name)
    return out


def run(doc, ground_registry=None):
    """Validate, then ask whichever instruments apply.

    THE INVARIANT, learned the hard way over an evening of one-at-a-time
    fixes: a document that PASSES validation may not make this function
    raise. The core's parsers throw on syntax they do not know, and every
    such throw arrived at the user as "internal studio error — the detail is
    in the server log", which tells them nothing and tells us only after
    they complain. Anything the instruments refuse becomes an issue
    addressed to the claim, in the same shape as every other issue. The
    underlying gap still gets fixed; it just stops being invisible while it
    waits."""
    doc = coerce(doc)
    issues = validate(doc)
    if any(i["level"] == "error" for i in issues):
        return {"ok": False, "issues": issues}
    rows = doc["rows"]
    demoted = []
    # Документ вправе объявить свой реестр сам; параметр вызова остаётся и
    # ПЕРЕВЕШИВАЕТ — на случай, когда допустимое решает не автор документа,
    # а тот, кто его принимает.
    if ground_registry is None:
        declared = (doc.get("grounds") or "").strip()
        if declared:
            ground_registry = {g.strip() for g in declared.split(",")
                               if g.strip()}
    if ground_registry is not None:
        rows, demoted = demote_unregistered(rows, set(ground_registry))
    claim = normalise((doc.get("claim") or "").strip(), rows)
    what, report = applies(doc), {}
    dead = set()

    if what["passport"]:
        system = to_system(rows)
        lfp, reports, comp_kind = zpassport.passports(system)
        dead = unredeemable(comp_kind)
        report["passport"] = [
            {"component": comp, "kind": kind, "detail": why}
            for comp, kind, why in reports]

    if what["numeric"] and claim:
        try:
            sheet = to_sheet(rows)
            q, m = parse_quantities(sheet)
            m.update(to_marking(rows))
            # An UNKNOWN in the table is a question, not a gap: `x=?` with
            # `x - 10 = 20` asks the solver for x, and the solver answers
            # with the provenance the answer inherited from the derivation.
            # Judging alone would have said "measure x", which is true and
            # useless when the sheet already determines it.
            unknown = any((r.get("value") or "").strip() == "?"
                          for r in numeric_rows(rows))
            if unknown:
                r = solve_claim(claim, q, m)
                solved = {n: {"lo": str(v["lo"]), "hi": str(v["hi"]),
                              "pinned": v["pinned"], "prov": v["prov"],
                              "from": v.get("from", []),
                              "weak": v.get("weak", [])}
                          for n, v in (r.get("solved") or {}).items()}
            else:
                r = judge_sheet_claim(claim, q, m)
                solved = {}
            report["numeric"] = {"disposition": r["disposition"],
                                 "lazy": r.get("lazy"),
                                 "next_check": r.get("next_check", []),
                                 "solved": solved, "claim": claim,
                                 "sheet": sheet}
            if unknown and not solved:
                names = [x["name"] for x in numeric_rows(rows)
                         if (x.get("value") or "").strip() == "?"]
                report["numeric"]["missing"] = missing_facts(claim, sheet,
                                                             names)
        except Exception as exc:
            issues.append(_issue("error", "E_UNREADABLE", "claim",
                                 f"the instruments could not read this "
                                 f"claim: {exc}"))
            return {"ok": False, "issues": issues}
    elif what["judge"]:
        try:
            # THROUGH the definitions, not around them. `to_marking` reports
            # marks and stops — correct about what a mark IS, and blind to
            # every value the sentences DETERMINE. Measured on the book
            # (2026-08-28): chapter 3 claims `honest_unknown & ~evasion`,
            # both defined from rows that are verified, and the judge called
            # it F/until-verification — a FALSE NEGATIVE it had been
            # reporting all along. Two chapters of eighteen move, both from
            # not-earned to earned. This is the architecture the draft
            # already states: quarantine is the Z-set of the lazy jump's
            # least fixed point, and ZTL is the greedy reading ON TOP of it.
            r = judge(claim, resolved_marking(rows))
        except Exception as exc:
            issues.append(_issue("error", "E_UNREADABLE", "claim",
                                 f"the instruments could not read this "
                                 f"claim: {exc}"))
            return {"ok": False, "issues": issues}
        report["judge"] = {"verdict": r["verdict"],
                           "disposition": r["disposition"],
                           "grade": r["grade"],
                           "unverified": sorted(r["unverified"])}
        # The grade stands as the core computed it; what the marking could
        # not say is added beside it rather than folded into it.
        touched = sorted(dead & names_in(claim))
        if touched and r["grade"] == "until-verification":
            report["judge"]["credit"] = "UNREDEEMABLE"
            report["judge"]["unredeemable"] = touched

    if what["epoch"]:
        # One crossing per declared event: everything held by that event's
        # clock returns to the mark AT ONCE (an event is not a sequence of
        # private misfortunes), and the claim is read on both sides of it.
        events = {}
        for r in rows:
            ev = (r.get("expires_on") or "").strip()
            if ev:
                events.setdefault(ev, []).append(r["name"])
        staged = []
        for ev in sorted(events):
            # The crossing is applied to the ROWS, not to the marking, so
            # that whatever leans on the expiring ground is recomputed
            # rather than left standing on a value that no longer has one.
            # Reading the marking alone is how the first draft of this floor
            # printed "survives" for every document with a definition in it:
            # `to_marking` drops defined rows, so expiring their ground moved
            # nothing the judge could see.
            gone = set(events[ev])
            rows_after = [dict(r, status="unverified", ground="")
                          if r["name"] in gone else r for r in rows]
            try:
                b = judge(claim, resolved_marking(rows))
                a = judge(claim, resolved_marking(rows_after))
            except Exception as exc:
                issues.append(_issue("error", "E_UNREADABLE", "claim",
                                     f"the epoch floor could not read this "
                                     f"claim: {exc}"))
                return {"ok": False, "issues": issues}
            staged.append({
                "event": ev,
                "expires": sorted(events[ev]),
                "before": {"verdict": b["verdict"], "grade": b["grade"]},
                "after": {"verdict": a["verdict"], "grade": a["grade"]},
                # SURVIVES means the conclusion is the same on both sides.
                # It is not praise: a verdict that survives every crossing
                # reads none of its grounds (EpochBoundary), so a survivor
                # here is either independently grounded or empty.
                "survives": b["verdict"] == a["verdict"]})
        report["epoch"] = staged

    if what["ledger"]:
        # Тот же инвариант, что у numeric-ветки выше, и он здесь не был
        # соблюдён: валидная глава книги роняла run интервальной строкой
        # (2026-08-27). Отказ прибора — issue к утверждению, не трейсбек.
        book = to_book(rows)
        try:
            judged = zbook.judge_book(book) if book else None
        except Exception as exc:
            issues.append(_issue("error", "E_UNREADABLE", "ledger",
                                 f"the ledger could not read these rows: "
                                 f"{exc}"))
            return {"ok": False, "issues": issues}
        if judged is not None:
            report["ledger"] = {
                "claims": {k: {"disposition": v["disposition"],
                               "assurance": v["assurance"]}
                           for k, v in judged.items()},
                "brackets": {g: list(iv) for g, iv
                             in zbook.trust_interval(book).items()},
                "naming": zbook.naming_assumption(book)}

    # КВИТАНЦИЯ ВЫДАЁТСЯ ВСЕГДА, когда есть что квитировать. Иначе она
    # остаётся доступной только тому, кто зовёт питон — а человек в тетради
    # её получить не может (нашёл КУРАТОР вопросом 2026-08-28, четвёртый за
    # день случай «построено и не позвано»). Чего не объявили — помечено
    # null, а не подразумевается.
    if claim and ("judge" in report or "numeric" in report):
        import warrant_receipt
        report["receipt"] = warrant_receipt.receipt(
            {"report": report}, doc, (doc.get("epoch") or ""),
            ground_registry=ground_registry)

    # БИРКА НА ЗАВИСЯЩИХ. Заработавшее на объявленном не прячется среди
    # заработавшего на предъявимом.
    стип = on_stipulation(rows, ground_registry) if ground_registry else []
    if стип:
        report["on_stipulation"] = стип

    if demoted:
        # ПОИМЁННО, не счётом: читатель должен видеть, ЧЬИ вердикты стояли
        # на непредъявленных основаниях, — иначе понижение неотличимо от
        # честного «не проверено», и ворота работают молча.
        report["demoted_grounds"] = sorted(demoted)
    return {"ok": True, "issues": issues, "applies": what, "report": report}
