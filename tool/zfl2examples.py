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
    # ------------------------------------- the paradox docket, entire
    # Every case §7 of the published docket promises is in the studio
    # (v1.1, DOI 10.5281/zenodo.21916017). Converted from the v1
    # examples, and `paper` names the case the paper names — the stand
    # asserts none of them can go missing, because the promise is
    # published and a studio without them makes the paper false.
    {"kind": "paradox", "paper": "Liar",
     "en": "Liar", "ru": "лжец",
     "doc": {
         "rows": [{"name": "L", "means": "", "status": "defined", "ground": "~(Tr(L))"}]}},
    {"kind": "paradox", "paper": "Barber (the liar in a barber's apron)",
     "en": "Barber (the liar in a barber's apron)", "ru": "брадобрей",
     "doc": {
         "rows": [{"name": "shaves", "means": "", "status": "defined", "ground": "~(Tr(shaves))"}]}},
    {"kind": "paradox", "paper": "Grelling's 'heterological'",
     "en": "Grelling's 'heterological'", "ru": "«гетерологичное» Греллинга",
     "doc": {
         "rows": [{"name": "het", "means": "", "status": "defined", "ground": "~(Tr(het))"}]}},
    {"kind": "paradox", "paper": "Russell",
     "en": "Russell", "ru": "Рассел",
     "doc": {
         "rows": [{"name": "a_in_a", "means": "", "status": "refuted", "ground": "the-story"}, {"name": "a_in_b", "means": "", "status": "refuted", "ground": "the-story"}, {"name": "a_in_R", "means": "", "status": "defined", "ground": "~(Tr(a_in_a))"}, {"name": "b_in_a", "means": "", "status": "refuted", "ground": "the-story"}, {"name": "b_in_b", "means": "", "status": "verified", "ground": "the-story"}, {"name": "b_in_R", "means": "", "status": "defined", "ground": "~(Tr(b_in_b))"}, {"name": "R_in_a", "means": "", "status": "refuted", "ground": "the-story"}, {"name": "R_in_b", "means": "", "status": "refuted", "ground": "the-story"}, {"name": "R_in_R", "means": "", "status": "defined", "ground": "~(Tr(R_in_R))"}]}},
    {"kind": "paradox", "paper": "Jourdain's postcard",
     "en": "Jourdain's postcard", "ru": "открытка Жордена",
     "doc": {
         "rows": [{"name": "front", "means": "", "status": "defined", "ground": "Tr(back)"}, {"name": "back", "means": "", "status": "defined", "ground": "~(Tr(front))"}]}},
    {"kind": "paradox", "paper": "Crocodile",
     "en": "Crocodile", "ru": "крокодил",
     "doc": {
         "rows": [{"name": "R", "means": "", "status": "defined", "ground": "Tr(M)"}, {"name": "M", "means": "", "status": "defined", "ground": "~(Tr(R))"}]}},
    {"kind": "paradox", "paper": "Odd 3-cycle",
     "en": "Odd 3-cycle", "ru": "нечётный трёхцикл",
     "doc": {
         "rows": [{"name": "a", "means": "", "status": "defined", "ground": "~(Tr(b))"}, {"name": "b", "means": "", "status": "defined", "ground": "~(Tr(c))"}, {"name": "c", "means": "", "status": "defined", "ground": "~(Tr(a))"}]}},
    {"kind": "paradox", "paper": "Curry (grounded falsum)",
     "en": "Curry (grounded falsum)", "ru": "Карри (ложь настоящая)",
     "doc": {
         "rows": [{"name": "g", "means": "", "status": "defined", "ground": "(Tr(g) ->  F)"}]}},
    {"kind": "paradox", "paper": "Curry (suspended falsum)",
     "en": "Curry (suspended falsum)", "ru": "Карри (ложь подвешенная)",
     "doc": {
         "rows": [{"name": "gamma", "means": "", "status": "defined", "ground": "(Tr(gamma) ->  Tr(bot))"}, {"name": "bot", "means": "", "status": "defined", "ground": "(Tr(s) &  ~(Tr(s)))"}, {"name": "s", "means": "", "status": "defined", "ground": "Tr(s)"}]}},
    {"kind": "paradox", "paper": "Strong liar (forced FALSE)",
     "en": "Strong liar (forced FALSE)", "ru": "усиленный лжец (вынужденно ЛОЖЬ)",
     "doc": {
         "rows": [{"name": "sigma", "means": "", "status": "defined", "ground": "(~(Tr(sigma)) &  Tr(sigma))"}]}},
    {"kind": "paradox", "paper": "Revenge / avenger (forced FALSE)",
     "en": "Revenge / avenger (forced FALSE)", "ru": "мститель (вынужденно ЛОЖЬ)",
     "doc": {
         "rows": [{"name": "mu", "means": "", "status": "defined", "ground": "not((Tr(mu) =  Tr(mu)))"}]}},
    {"kind": "paradox", "paper": "Henkin-style sentence (forced TRUE)",
     "en": "Henkin-style sentence (forced TRUE)", "ru": "предложение Хенкина (вынужденно ИСТИНА)",
     "doc": {
         "rows": [{"name": "h", "means": "", "status": "defined", "ground": "(Tr(h) ->  Tr(h))"}]}},
    {"kind": "paradox", "paper": "Truth-teller",
     "en": "Truth-teller", "ru": "правдоруб",
     "doc": {
         "rows": [{"name": "tau", "means": "", "status": "defined", "ground": "Tr(tau)"}]}},
    {"kind": "paradox", "paper": "Russell's twin S∈S",
     "en": "Russell's twin S∈S", "ru": "близнец Рассела S∈S",
     "doc": {
         "rows": [{"name": "S_in_S", "means": "", "status": "defined", "ground": "Tr(S_in_S)"}]}},
    {"kind": "paradox", "paper": "Crocodile control (optimistic mother)",
     "en": "Crocodile control (optimistic mother)", "ru": "крокодил, контроль (мать-оптимистка)",
     "doc": {
         "rows": [{"name": "R", "means": "", "status": "defined", "ground": "Tr(M)"}, {"name": "M", "means": "", "status": "defined", "ground": "Tr(R)"}]}},
    {"kind": "paradox", "paper": "Even 2-cycle",
     "en": "Even 2-cycle", "ru": "чётный двуцикл",
     "doc": {
         "rows": [{"name": "A", "means": "", "status": "defined", "ground": "~(Tr(B))"}, {"name": "B", "means": "", "status": "defined", "ground": "~(Tr(A))"}]}},
    {"kind": "paradox", "paper": "Even 4-cycle",
     "en": "Even 4-cycle", "ru": "чётный четырёхцикл",
     "doc": {
         "rows": [{"name": "a", "means": "", "status": "defined", "ground": "~(Tr(b))"}, {"name": "b", "means": "", "status": "defined", "ground": "~(Tr(c))"}, {"name": "c", "means": "", "status": "defined", "ground": "~(Tr(d))"}, {"name": "d", "means": "", "status": "defined", "ground": "~(Tr(a))"}]}},
    {"kind": "paradox", "paper": "Yablo (truncated at 3)",
     "en": "Yablo (truncated at 3)", "ru": "Ябло (обрезанный до 3)",
     "doc": {
         "rows": [{"name": "s0", "means": "", "status": "defined", "ground": "(~(Tr(s1)) &  ~(Tr(s2)))"}, {"name": "s1", "means": "", "status": "defined", "ground": "~(Tr(s2))"}, {"name": "s2", "means": "", "status": "verified", "ground": "the-story"}]}},
    {"kind": "paradox", "paper": "Contingent liar — world A (harmless)",
     "en": "Contingent liar — world A (harmless)", "ru": "контингентный лжец — мир A (безобидный)",
     "doc": {
         "rows": [{"name": "S", "means": "", "status": "defined", "ground": "~(Tr(J))"}, {"name": "J", "means": "", "status": "defined", "ground": "Tr(g)"}, {"name": "g", "means": "", "status": "verified", "ground": "the-story"}]}},
    {"kind": "paradox", "paper": "Contingent liar — world B (unlucky)",
     "en": "Contingent liar — world B (unlucky)", "ru": "контингентный лжец — мир B (неудачный)",
     "doc": {
         "rows": [{"name": "S", "means": "", "status": "defined", "ground": "~(Tr(J))"}, {"name": "J", "means": "", "status": "defined", "ground": "Tr(S)"}]}},
    {"kind": "paradox", "paper": "Contingent liar — world C (unverified)",
     "en": "Contingent liar — world C (unverified)", "ru": "контингентный лжец — мир C (непроверенный)",
     "doc": {
         "rows": [{"name": "J", "means": "what Jones said is true", "status": "unverified"}, {"name": "S", "means": "", "status": "defined", "ground": "~(Tr(J))"}]}},
    {"kind": "paradox", "paper": "Ship of Theseus: the title contest",
     "en": "Ship of Theseus: the title contest", "ru": "Корабль Тесея: спор о титуле",
     "doc": {
         "rows": [{"name": "theA", "means": "", "status": "defined", "ground": "~(Tr(theB))"}, {"name": "theB", "means": "", "status": "defined", "ground": "~(Tr(theA))"}]}},
    {"kind": "paradox", "paper": "Agrippa's dogma (foundation with a passport)",
     "en": "Agrippa's dogma (foundation with a passport)", "ru": "догма Агриппы (основание с паспортом)",
     "doc": {
         "rows": [{"name": "p", "means": "", "status": "defined", "ground": "Tr(f)"}, {"name": "f", "means": "", "status": "defined", "ground": "Tr(f)"}]}},
    {"kind": "paradox", "paper": "Same person? (corecursion, all observations match)",
     "en": "Same person? (corecursion, all observations match)", "ru": "тот же человек? (корекурсия)",
     "doc": {
         "rows": [{"name": "obs", "means": "every observation so far matches", "status": "verified", "ground": "the-story"}, {"name": "S", "means": "", "status": "defined", "ground": "(Tr(obs) &  Tr(S))"}]}},
    {"kind": "everyday", "paper": "Sensor",
     "en": "Sensor", "ru": "датчик",
     "doc": {
         "rows": [{"name": "overheat", "means": "the sensor reads overheating", "status": "unverified"}, {"name": "shutdown", "means": "the shutdown fires", "status": "unverified"}],
         "claim": "(overheat ->  shutdown)"}},
    {"kind": "everyday", "paper": "Modus ponens (Carroll's tortoise)",
     "en": "Modus ponens (Carroll's tortoise)", "ru": "modus ponens (черепаха Кэрролла)",
     "doc": {
         "rows": [{"name": "p", "means": "the premise p holds", "status": "unverified"}, {"name": "q", "means": "the conclusion q holds", "status": "unverified"}],
         "claim": "(((p -> q) & p) -> q)"}},

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
