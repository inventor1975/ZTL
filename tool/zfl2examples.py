# -*- coding: utf-8 -*-
"""
The examples, in two levels — a KIND and then a case.

v1 had one long drop-down of twenty-odd entries, which is a list you scroll
rather than a list you choose from. Two steps: what kind of question is this,
then which one. The kinds are not decoration — they are the four things this
studio can be asked, and seeing them named is itself the shortest possible
account of what the instrument does.

EVERY EXAMPLE IS CHECKED, not merely stored: `tool/test_zfl2.py` validates
each and runs it, so an example that stopped working cannot ship. An
example is a promise about the machine, and a broken one is a lie told to
whoever clicked it.
"""

KINDS = {
    "paradox": {"en": "paradoxes and self-reference",
                "ru": "парадоксы и самоссылка"},
    "audit": {"en": "invoices and audit", "ru": "накладные и аудит"},
    "numbers": {"en": "asking for a number", "ru": "спросить число"},
    "everyday": {"en": "everyday reasoning", "ru": "обычные рассуждения"},
}

EXAMPLES = [
    # ---------------------------------------------------------- paradoxes
    {"kind": "paradox",
     "en": "the liar", "ru": "лжец",
     "doc": {"rows": [
         {"name": "L", "means": "this sentence is false",
          "status": "defined", "ground": "~Tr(L)"}]}},
    {"kind": "paradox",
     "en": "the truth-teller", "ru": "правдоруб",
     "doc": {"rows": [
         {"name": "T1", "means": "this sentence is true",
          "status": "defined", "ground": "Tr(T1)"}]}},
    {"kind": "paradox",
     "en": "the barber", "ru": "брадобрей",
     "doc": {"rows": [
         {"name": "shaves", "means": "the barber shaves himself",
          "status": "defined", "ground": "~Tr(shaves)"}]}},
    {"kind": "paradox",
     "en": "an even cycle — a blank, not a paradox",
     "ru": "чётный круг — бланк, а не парадокс",
     "doc": {"rows": [
         {"name": "A", "means": "B is false", "status": "defined",
          "ground": "~Tr(B)"},
         {"name": "B", "means": "A is false", "status": "defined",
          "ground": "~Tr(A)"}]}},
    {"kind": "paradox",
     "en": "a claim resting on the liar",
     "ru": "утверждение, стоящее на лжеце",
     "doc": {"rows": [
         {"name": "L", "means": "this sentence is false",
          "status": "defined", "ground": "~Tr(L)"},
         {"name": "g", "means": "the grass is green", "status": "defined",
          "ground": "~Tr(L)"}]}},

    # -------------------------------------------------------------- audit
    {"kind": "audit",
     "en": "a line against its ceiling", "ru": "строка против потолка",
     "doc": {"rows": [
         {"name": "line", "means": "the invoice line", "status": "verified",
          "ground": "inv-17", "value": "1500", "unit": "RUB"},
         {"name": "budget", "means": "the ceiling", "status": "verified",
          "ground": "order-4", "value": "5000", "unit": "RUB"}],
         "claim": "line <= budget"}},
    {"kind": "audit",
     "en": "two lines on ONE document — what falls together",
     "ru": "две строки на ОДНОМ документе — что падает вместе",
     "doc": {"rows": [
         {"name": "a", "means": "the first line", "status": "verified",
          "ground": "inv-17", "value": "100", "unit": "RUB"},
         {"name": "b", "means": "the second line", "status": "verified",
          "ground": "inv-17", "value": "200", "unit": "RUB"}],
         "claim": "a <= b"}},
    {"kind": "audit",
     "en": "a warranty that expires", "ru": "гарантия, которая истекает",
     "doc": {"rows": [
         {"name": "fee", "means": "the fee under warranty",
          "status": "verified", "ground": "cert-7",
          "ground_kind": "certificate", "value": "100", "unit": "RUB"},
         {"name": "paid", "means": "what was paid", "status": "verified",
          "ground": "deed", "value": "80", "unit": "RUB"}],
         "claim": "paid <= fee"}},
    {"kind": "audit",
     "en": "an unverified figure in the sheet",
     "ru": "непроверенная цифра в листе",
     "doc": {"rows": [
         {"name": "quoted", "means": "the figure quoted to us",
          "status": "unverified", "value": "1200", "unit": "RUB"},
         {"name": "cap", "means": "the agreed cap", "status": "verified",
          "ground": "contract", "value": "1000", "unit": "RUB"}],
         "claim": "quoted <= cap"}},
    {"kind": "audit",
     "en": "metres against roubles — the fourth corner",
     "ru": "метры против рублей — четвёртый угол",
     "doc": {"rows": [
         {"name": "area", "means": "the area", "status": "verified",
          "ground": "plan", "value": "3", "unit": "m2"},
         {"name": "fee", "means": "the fee", "status": "verified",
          "ground": "reg-7", "value": "5", "unit": "RUB"}],
         "claim": "fee == area"}},

    # ------------------------------------------------------------ numbers
    {"kind": "numbers",
     "en": "solve for x", "ru": "найти x",
     "doc": {"rows": [
         {"name": "x", "means": "the unknown", "status": "unverified",
          "value": "?"}],
         "claim": "x - 10 = 20"}},
    {"kind": "numbers",
     "en": "the missing line of an invoice",
     "ru": "недостающая строка накладной",
     "doc": {"rows": [
         {"name": "total", "means": "the invoice total", "status": "verified",
          "ground": "inv-19", "value": "4500", "unit": "RUB"},
         {"name": "a", "means": "the first line", "status": "verified",
          "ground": "inv-17", "value": "3000", "unit": "RUB"},
         {"name": "b", "means": "the missing line", "status": "unverified",
          "value": "?", "unit": "RUB"}],
         "claim": "sum(a,b) = total"}},
    {"kind": "numbers",
     "en": "a school word problem, in candies",
     "ru": "школьная задача, в конфетах",
     "doc": {"rows": [
         {"name": "masha", "means": "what Masha has left after Vasya",
          "status": "verified", "ground": "the-story", "value": "2",
          "unit": "candies"},
         {"name": "give", "means": "how many she gives Petya",
          "status": "unverified", "value": "?", "unit": "candies"}],
         "claim": "masha - give = give"}},
    {"kind": "numbers",
     "en": "a box that stays a box", "ru": "коробка, которая остаётся коробкой",
     "doc": {"rows": [
         {"name": "age", "means": "the age", "status": "unverified",
          "value": "?", "scale": "int"},
         {"name": "lo", "means": "the lower bound", "status": "verified",
          "ground": "form", "value": "11"},
         {"name": "hi", "means": "the upper bound", "status": "verified",
          "ground": "form", "value": "13"}],
         "claim": "lo <= age & age <= hi"}},
    {"kind": "numbers",
     "en": "a third that no scale of hundredths holds",
     "ru": "треть, которой не вмещают сотые",
     "doc": {"rows": [
         {"name": "share", "means": "one third of the whole",
          "status": "unverified", "value": "?", "scale": "decimal2"},
         {"name": "whole", "means": "the whole", "status": "verified",
          "ground": "deed", "value": "8"}],
         "claim": "share * 3 = whole"}},

    # ----------------------------------------------------------- everyday
    {"kind": "everyday",
     "en": "if it rains I take an umbrella",
     "ru": "если дождь — беру зонт",
     "doc": {"rows": [
         {"name": "rain", "means": "it is raining", "status": "unverified"},
         {"name": "umbrella", "means": "I take an umbrella",
          "status": "unverified"}],
         "claim": "rain -> umbrella"}},
    {"kind": "everyday",
     "en": "a promise on an unverified condition",
     "ru": "обещание на непроверенном условии",
     "doc": {"rows": [
         {"name": "paid", "means": "the invoice was paid",
          "status": "unverified"},
         {"name": "ship", "means": "we ship the goods",
          "status": "verified", "ground": "waybill-3"}],
         "claim": "paid -> ship"}},
    {"kind": "everyday",
     "en": "what one verification buys", "ru": "что покупает одна проверка",
     "doc": {"rows": [
         {"name": "signed", "means": "the contract is signed",
          "status": "verified", "ground": "scan-12"},
         {"name": "delivered", "means": "the goods arrived",
          "status": "unverified"}],
         "claim": "signed & delivered"}},
]


def catalogue(lang="en"):
    """Kinds and their cases, for the two drop-downs."""
    kinds = [{"key": k, "label": v.get(lang, v["en"])}
             for k, v in KINDS.items()]
    items = [{"kind": e["kind"], "label": e.get(lang, e["en"]), "doc": e["doc"]}
             for e in EXAMPLES]
    return {"kinds": kinds, "items": items}
