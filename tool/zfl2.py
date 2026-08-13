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

COLUMNS = [
    {
        "key": "name", "type": "text", "required": True, "advanced": False,
        "en": ("name", "what we call it; formulas use this"),
        "ru": ("имя", "как называем; им же пользуемся в формулах"),
        "eg": ["line", "budget", "L"],
    },
    {
        "key": "means", "type": "text", "required": False, "advanced": False,
        "en": ("means", "what it MEANS for this to be true"),
        "ru": ("значит", "что означает истинность этого имени"),
        "eg": ["the invoice line", "this sentence is false"],
        # not decoration: the gloss is the polarity auditor. `fresh` already
        # means "not revoked", so "not fresh" asserts a positive fact —
        # names lie, glosses do not.
    },
    {
        "key": "status", "type": "choice", "required": True, "advanced": False,
        "options": ["verified", "refuted", "unverified", "defined"],
        "en": ("status", "where it stands with us"),
        "ru": ("статус", "откуда оно у нас"),
        "labels": {
            "en": {"verified": "verified", "refuted": "refuted",
                   "unverified": "not verified", "defined": "defined"},
            "ru": {"verified": "проверено", "refuted": "опровергнуто",
                   "unverified": "не проверено", "defined": "определено"},
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
        "eg": ["inv-17", "~Tr(L)"],
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
        "key": "ground_kind", "type": "choice", "required": False,
        "advanced": False, "default": "document",
        "options": ["document", "act", "certificate", "row"],
        "en": ("kind of ground", "a document unless you say otherwise"),
        "ru": ("вид основания", "документ, если не сказано иное"),
        "labels": {
            "en": {"document": "document", "act": "act (nothing to withdraw)",
                   "certificate": "certificate (expires)",
                   "row": "another row"},
            "ru": {"document": "документ", "act": "акт (отзывать нечего)",
                   "certificate": "сертификат (истекает)",
                   "row": "другая строка"},
        },
    },
    {
        "key": "value", "type": "text", "required": False, "advanced": False,
        "en": ("value", "a number, an interval [0,10], or ? for unknown"),
        "ru": ("величина", "число, интервал [0,10] или ? для неизвестного"),
        "eg": ["1500", "[0,10]", "?"],
    },
    {
        "key": "unit", "type": "text", "required": False, "advanced": False,
        "en": ("unit", "only with a value; metres never meet roubles"),
        "ru": ("единица", "только с величиной; метры не встречаются с рублями"),
        "eg": ["RUB", "m", "m2"],
    },
    {
        "key": "scale", "type": "choice", "required": False, "advanced": False,
        "default": "", "options": ["", "int", "decimal2", "frac3"],
        "en": ("scale", "what it rounds to"),
        "ru": ("шкала", "до чего округляем"),
        "labels": {
            "en": {"": "exact", "int": "whole", "decimal2": "hundredths",
                   "frac3": "thirds"},
            "ru": {"": "точно", "int": "целые", "decimal2": "сотые",
                   "frac3": "трети"},
        },
    },
    {
        "key": "sample", "type": "bool", "required": False, "advanced": True,
        "default": False,
        "en": ("separate measurements",
               "each occurrence is its own act of measuring"),
        "ru": ("отдельные измерения",
               "каждое вхождение — свой акт измерения"),
    },
]

DOC_FIELDS = [
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
        return out
    return {"columns": [render(c) for c in COLUMNS],
            "document": [render(c) for c in DOC_FIELDS]}


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
    out = {"claim": str(doc.get("claim") or ""),
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
            continue
        ground = (r.get("ground") or "").strip()
        if status in ("verified", "refuted", "defined") and not ground:
            issues.append(_issue("error", "E_NOGROUND", f"{at} / ground",
                                 "a verified, refuted or defined name has to "
                                 "say what backs it"))
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
        kind = (r.get("ground_kind") or "document").strip()
        if kind not in GROUND_KINDS:
            issues.append(_issue("error", "E_KIND", f"{at} / kind of ground",
                                 f"kind must be one of {GROUND_KINDS}"))
        if status == "defined":
            try:
                _formula(ground, {})
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
        system[name] = _formula(r.get("ground") or "", {})
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
        "judge": bool((doc.get("claim") or "").strip()),
    }


def run(doc):
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
    claim = normalise((doc.get("claim") or "").strip(), rows)
    what, report = applies(doc), {}

    if what["passport"]:
        system = to_system(rows)
        lfp, reports, _ = zpassport.passports(system)
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
        except Exception as exc:
            issues.append(_issue("error", "E_UNREADABLE", "claim",
                                 f"the instruments could not read this "
                                 f"claim: {exc}"))
            return {"ok": False, "issues": issues}
    elif what["judge"]:
        try:
            r = judge(claim, to_marking(rows))
        except Exception as exc:
            issues.append(_issue("error", "E_UNREADABLE", "claim",
                                 f"the instruments could not read this "
                                 f"claim: {exc}"))
            return {"ok": False, "issues": issues}
        report["judge"] = {"verdict": r["verdict"],
                           "disposition": r["disposition"],
                           "grade": r["grade"],
                           "unverified": sorted(r["unverified"])}

    if what["ledger"]:
        book = to_book(rows)
        if book:
            judged = zbook.judge_book(book)
            report["ledger"] = {
                "claims": {k: {"disposition": v["disposition"],
                               "assurance": v["assurance"]}
                           for k, v in judged.items()},
                "brackets": {g: list(iv) for g, iv
                             in zbook.trust_interval(book).items()},
                "naming": zbook.naming_assumption(book)}

    return {"ok": True, "issues": issues, "applies": what, "report": report}
