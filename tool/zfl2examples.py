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
     "ask_en": "This sentence is false.",
     "ask_ru": "Это предложение ложно.",
     "en": "Liar", "ru": "лжец",
     "doc": {
         "rows": [{"name": "L", "means": "это предложение ложно", "status": "defined", "ground": "~(Tr(L))"}]}},
    {"kind": "paradox", "paper": "Barber (the liar in a barber's apron)",
     "ask_en": "The barber shaves exactly those who do not shave themselves. Does he shave himself?",
     "ask_ru": "Брадобрей бреет ровно тех, кто не бреется сам. Бреет ли он себя?",
     "en": "Barber (the liar in a barber's apron)", "ru": "брадобрей",
     "doc": {
         "rows": [{"name": "shaves", "means": "брадобрей бреет самого себя", "status": "defined", "ground": "~(Tr(shaves))"}]}},
    {"kind": "paradox", "paper": "Grelling's 'heterological'",
     "ask_en": "'Heterological' means 'not applying to itself'. Is 'heterological' heterological?",
     "ask_ru": "«Гетерологичное» значит «неприменимое к себе». Гетерологично ли «гетерологичное»?",
     "en": "Grelling's 'heterological'", "ru": "«гетерологичное» Греллинга",
     "doc": {
         "rows": [{"name": "het", "means": "«гетерологичное» не описывает само себя", "status": "defined", "ground": "~(Tr(het))"}]}},
    {"kind": "paradox", "paper": "Russell",
     "ask_en": "The set of all sets not containing themselves: does it contain itself? Universe: a = empty, b = {b}, R.",
     "ask_ru": "Множество всех множеств, не содержащих себя: содержит ли оно себя?",
     "en": "Russell", "ru": "Рассел",
     "doc": {
         "rows": [{"name": "a_in_a", "means": "a принадлежит a", "status": "refuted", "ground": "the-story"}, {"name": "a_in_b", "means": "a принадлежит b", "status": "refuted", "ground": "the-story"}, {"name": "a_in_R", "means": "a принадлежит R", "status": "defined", "ground": "~(Tr(a_in_a))"}, {"name": "b_in_a", "means": "b принадлежит a", "status": "refuted", "ground": "the-story"}, {"name": "b_in_b", "means": "b принадлежит b", "status": "verified", "ground": "the-story"}, {"name": "b_in_R", "means": "b принадлежит R", "status": "defined", "ground": "~(Tr(b_in_b))"}, {"name": "R_in_a", "means": "R принадлежит a", "status": "refuted", "ground": "the-story"}, {"name": "R_in_b", "means": "R принадлежит b", "status": "refuted", "ground": "the-story"}, {"name": "R_in_R", "means": "R принадлежит самому себе", "status": "defined", "ground": "~(Tr(R_in_R))"}]}},
    {"kind": "paradox", "paper": "Jourdain's postcard",
     "ask_en": "Front of the card: 'the sentence on the back is true'. Back: 'the sentence on the front is false'. Note the oscillation period: 4, not the liar's 2.",
     "ask_ru": "На одной стороне: «написанное на обороте — правда». На обороте: «написанное на лицевой — ложь».",
     "en": "Jourdain's postcard", "ru": "открытка Жордена",
     "doc": {
         "rows": [{"name": "front", "means": "написанное на обороте — правда", "status": "defined", "ground": "Tr(back)"}, {"name": "back", "means": "написанное на лицевой стороне — ложь", "status": "defined", "ground": "~(Tr(front))"}]}},
    {"kind": "paradox", "paper": "Crocodile",
     "ask_en": "The crocodile returns the child if and only if the mother guesses what he will do. The mother: 'you will not return it'. Same shape as Jourdain's postcard — and the deal itself never earns truth: the contract is void.",
     "ask_ru": "Крокодил обещает вернуть ребёнка, если мать угадает, что он сделает. Она говорит: «не вернёшь».",
     "en": "Crocodile", "ru": "крокодил",
     "doc": {
         "rows": [{"name": "R", "means": "крокодил возвращает ребёнка", "status": "defined", "ground": "Tr(M)"}, {"name": "M", "means": "мать угадала, что он сделает", "status": "defined", "ground": "~(Tr(R))"}]}},
    {"kind": "paradox", "paper": "Odd 3-cycle",
     "ask_en": "Three sentences in a ring, each denying the next: odd parity, no consistent solution. Vicious is the parity, not the circle.",
     "ask_ru": "Три предложения по кругу, каждое отрицает следующее.",
     "en": "Odd 3-cycle", "ru": "нечётный трёхцикл",
     "doc": {
         "rows": [{"name": "a", "means": "первое предложение цикла истинно", "status": "defined", "ground": "~(Tr(b))"}, {"name": "b", "means": "второе предложение цикла истинно", "status": "defined", "ground": "~(Tr(c))"}, {"name": "c", "means": "третье предложение цикла истинно", "status": "defined", "ground": "~(Tr(a))"}]}},
    {"kind": "paradox", "paper": "Curry (grounded falsum)",
     "ask_en": "'If this sentence is true, then falsehood.' With a real, grounded falsum Curry IS the liar in an arrow costume.",
     "ask_ru": "«Если это предложение истинно, то невозможное имеет место» — при настоящей лжи.",
     "en": "Curry (grounded falsum)", "ru": "Карри (ложь настоящая)",
     "doc": {
         "rows": [{"name": "g", "means": "предложение Карри истинно", "status": "defined", "ground": "(Tr(g) ->  F)"}]}},
    {"kind": "paradox", "paper": "Curry (suspended falsum)",
     "ask_en": "The same Curry, but its 'falsum' is defined over an unsettled base: the refusal is INHERITED, and the culprit is named. Curry's passport depends on what feeds the arrow.",
     "ask_ru": "То же предложение Карри, но «невозможное» само не проверено.",
     "en": "Curry (suspended falsum)", "ru": "Карри (ложь подвешенная)",
     "doc": {
         "rows": [{"name": "gamma", "means": "предложение Карри истинно", "status": "defined", "ground": "(Tr(gamma) ->  Tr(bot))"}, {"name": "bot", "means": "невозможное имеет место", "status": "defined", "ground": "(Tr(s) &  ~(Tr(s)))"}, {"name": "s", "means": "следствие Карри истинно", "status": "defined", "ground": "Tr(s)"}]}},
    {"kind": "paradox", "paper": "Strong liar (forced FALSE)",
     "ask_en": "'This sentence is false AND this sentence is true.' Intuition says: worse than the liar. Measurement says: tamer — exactly one consistent solution, forced false.",
     "ask_ru": "«Это предложение не истинно» — усиленный лжец.",
     "en": "Strong liar (forced FALSE)", "ru": "усиленный лжец (вынужденно ЛОЖЬ)",
     "doc": {
         "rows": [{"name": "sigma", "means": "это предложение не истинно", "status": "defined", "ground": "(~(Tr(sigma)) &  Tr(sigma))"}]}},
    {"kind": "paradox", "paper": "Revenge / avenger (forced FALSE)",
     "ask_en": "'This sentence is not equivalent to itself.' One consistent solution: forced false. (The validator will flag the degenerate xnor(mu,mu) — that degeneracy IS the sentence.)",
     "ask_ru": "«Это предложение не является заработанной истиной» — мститель.",
     "en": "Revenge / avenger (forced FALSE)", "ru": "мститель (вынужденно ЛОЖЬ)",
     "doc": {
         "rows": [{"name": "mu", "means": "это предложение не является заработанной истиной", "status": "defined", "ground": "not((Tr(mu) =  Tr(mu)))"}]}},
    {"kind": "paradox", "paper": "Henkin-style sentence (forced TRUE)",
     "ask_en": "'If this sentence is true, then this sentence is true.' The strong liar's mirror: one solution, forced TRUE.",
     "ask_ru": "«Это предложение доказуемо» — предложение Хенкина.",
     "en": "Henkin-style sentence (forced TRUE)", "ru": "предложение Хенкина (вынужденно ИСТИНА)",
     "doc": {
         "rows": [{"name": "h", "means": "это предложение доказуемо", "status": "defined", "ground": "(Tr(h) ->  Tr(h))"}]}},
    {"kind": "paradox", "paper": "Truth-teller",
     "ask_en": "This sentence is true.",
     "ask_ru": "«Это предложение истинно» — правдоруб.",
     "en": "Truth-teller", "ru": "правдоруб",
     "doc": {
         "rows": [{"name": "tau", "means": "это предложение истинно", "status": "defined", "ground": "Tr(tau)"}]}},
    {"kind": "paradox", "paper": "Russell's twin S∈S",
     "ask_en": "The set of all sets that DO contain themselves: does it contain itself? The truth-teller of set theory — two honest answers, choose by decree. Type theory bans this curable twin together with the incurable R.",
     "ask_ru": "Множество, определённое как принадлежащее самому себе.",
     "en": "Russell's twin S∈S", "ru": "близнец Рассела S∈S",
     "doc": {
         "rows": [{"name": "S_in_S", "means": "множество S принадлежит самому себе", "status": "defined", "ground": "Tr(S_in_S)"}]}},
    {"kind": "paradox", "paper": "Crocodile control (optimistic mother)",
     "ask_en": "Flip the mother's prediction to 'you WILL return it': one negation vanishes, parity flips, the sentence becomes a blank. Note WHO fills it: the deal binds nobody — the crocodile does as he pleases in both solutions.",
     "ask_ru": "Тот же крокодил, но мать говорит: «вернёшь». Контроль.",
     "en": "Crocodile control (optimistic mother)", "ru": "крокодил, контроль (мать-оптимистка)",
     "doc": {
         "rows": [{"name": "R", "means": "крокодил возвращает ребёнка", "status": "defined", "ground": "Tr(M)"}, {"name": "M", "means": "мать угадала, что он сделает", "status": "defined", "ground": "Tr(R)"}]}},
    {"kind": "paradox", "paper": "Even 2-cycle",
     "ask_en": "Two sentences denying each other: even parity, two lawful solutions, stipulate either.",
     "ask_ru": "Два предложения, каждое отрицает другое.",
     "en": "Even 2-cycle", "ru": "чётный двуцикл",
     "doc": {
         "rows": [{"name": "A", "means": "A истинно", "status": "defined", "ground": "~(Tr(B))"}, {"name": "B", "means": "B истинно", "status": "defined", "ground": "~(Tr(A))"}]}},
    {"kind": "paradox", "paper": "Even 4-cycle",
     "ask_en": "Four negations around the ring: still even, still a blank.",
     "ask_ru": "Четыре предложения по кругу, чётное число отрицаний.",
     "en": "Even 4-cycle", "ru": "чётный четырёхцикл",
     "doc": {
         "rows": [{"name": "a", "means": "первое предложение цикла истинно", "status": "defined", "ground": "~(Tr(b))"}, {"name": "b", "means": "второе предложение цикла истинно", "status": "defined", "ground": "~(Tr(c))"}, {"name": "c", "means": "третье предложение цикла истинно", "status": "defined", "ground": "~(Tr(d))"}, {"name": "d", "means": "четвёртое предложение цикла истинно", "status": "defined", "ground": "~(Tr(a))"}]}},
    {"kind": "paradox", "paper": "Yablo (truncated at 3)",
     "ask_en": "An infinite queue, each sentence saying 'everyone after me lies'. EVERY finite truncation is grounded — no quarantine at all: the paradoxicality lives only in the actual infinity. Extend the queue and see for yourself.",
     "ask_ru": "Ябло, обрезанный до трёх: каждое говорит, что все последующие ложны.",
     "en": "Yablo (truncated at 3)", "ru": "Ябло (обрезанный до 3)",
     "doc": {
         "rows": [{"name": "s0", "means": "ни одно из последующих не истинно", "status": "defined", "ground": "(~(Tr(s1)) &  ~(Tr(s2)))"}, {"name": "s1", "means": "ни одно из последующих не истинно", "status": "defined", "ground": "~(Tr(s2))"}, {"name": "s2", "means": "ни одно из последующих не истинно", "status": "verified", "ground": "the-story"}]}},
    {"kind": "paradox", "paper": "Contingent liar — world A (harmless)",
     "ask_en": "Smith: 'what Jones said is false.' Jones happened to say a truth about grass. Smith's sentence is plain false — everything grounded, case closed.",
     "ask_ru": "Смит говорит «Джонс лжёт», Джонс говорит правду о траве. Мир, где всё безобидно.",
     "en": "Contingent liar — world A (harmless)", "ru": "контингентный лжец — мир A (безобидный)",
     "doc": {
         "rows": [{"name": "S", "means": "сказанное Смитом истинно", "status": "defined", "ground": "~(Tr(J))"}, {"name": "J", "means": "сказанное Джонсом истинно", "status": "defined", "ground": "Tr(g)"}, {"name": "g", "means": "предложение Карри истинно", "status": "verified", "ground": "the-story"}]}},
    {"kind": "paradox", "paper": "Contingent liar — world B (unlucky)",
     "ask_en": "Same Smith sentence — but Jones happened to say 'Smith speaks truly'. Two honest people close Jourdain's carousel without knowing it. A paradox is an event, not a text (Kripke).",
     "ask_ru": "Тот же Смит, но Джонс говорит «Смит прав». Круг замкнулся.",
     "en": "Contingent liar — world B (unlucky)", "ru": "контингентный лжец — мир B (неудачный)",
     "doc": {
         "rows": [{"name": "S", "means": "сказанное Смитом истинно", "status": "defined", "ground": "~(Tr(J))"}, {"name": "J", "means": "сказанное Джонсом истинно", "status": "defined", "ground": "Tr(S)"}]}},
    {"kind": "paradox", "paper": "Contingent liar — world C (unverified)",
     "ask_en": "Same Smith sentence; what Jones said is not yet verified. The refusal is CONDITIONAL, and the culprit is named: verify Jones and the case resolves either way.",
     "ask_ru": "Тот же Смит, но что сказал Джонс — неизвестно.",
     "en": "Contingent liar — world C (unverified)", "ru": "контингентный лжец — мир C (непроверенный)",
     "doc": {
         "rows": [{"name": "J", "means": "what Jones said is true", "status": "unverified"}, {"name": "S", "means": "сказанное Смитом истинно", "status": "defined", "ground": "~(Tr(J))"}]}},
    {"kind": "paradox", "paper": "Ship of Theseus: the title contest",
     "ask_en": "Repaired ship A and reassembled ship B each claim: 'the real one is me, because it is not him'. An even cycle — two lawful decrees, no paradox anywhere. (The criterion-free 'same, in itself' is the truth-teller: try same := Tr(same).)",
     "ask_ru": "Кто носит титул «тот самый корабль» — A или B?",
     "en": "Ship of Theseus: the title contest", "ru": "Корабль Тесея: спор о титуле",
     "doc": {
         "rows": [{"name": "theA", "means": "титул принадлежит кораблю A", "status": "defined", "ground": "~(Tr(theB))"}, {"name": "theB", "means": "титул принадлежит кораблю B", "status": "defined", "ground": "~(Tr(theA))"}]}},
    {"kind": "paradox", "paper": "Agrippa's dogma (foundation with a passport)",
     "ask_en": "A self-supporting foundation f := f with a dependent claim on top: the foundation is stipulable, and the dependent's refusal names its culprit.",
     "ask_ru": "Утверждение стоит на фундаменте, который держится сам собой.",
     "en": "Agrippa's dogma (foundation with a passport)", "ru": "догма Агриппы (основание с паспортом)",
     "doc": {
         "rows": [{"name": "p", "means": "утверждение, стоящее на фундаменте", "status": "defined", "ground": "Tr(f)"}, {"name": "f", "means": "фундамент держится сам собой", "status": "defined", "ground": "Tr(f)"}]}},
    {"kind": "paradox", "paper": "Same person? (corecursion, all observations match)",
     "ask_en": "'The same person' = matches now AND the same henceforth: S := obs AND S. With every observation matching, the core never says 'yes' — only 'decide'. Flip obs to F and watch identity ground to false instantly: refutable by fact, confirmable only by decree.",
     "ask_ru": "Тот же ли это человек, если все наблюдения совпадают?",
     "en": "Same person? (corecursion, all observations match)", "ru": "тот же человек? (корекурсия)",
     "doc": {
         "rows": [{"name": "obs", "means": "every observation so far matches", "status": "verified", "ground": "the-story"}, {"name": "S", "means": "сказанное Смитом истинно", "status": "defined", "ground": "(Tr(obs) &  Tr(S))"}]}},
    {"kind": "everyday", "paper": "Sensor",
     "ask_en": "An unverified sensor reports overheating; if overheating, the shutdown fires. Will it fire? (Also try the one-line human syntax: assert overheat impl shutdown)",
     "ask_ru": "Датчик показывает перегрев — должно ли сработать отключение?",
     "en": "Sensor", "ru": "датчик",
     "doc": {
         "rows": [{"name": "overheat", "means": "the sensor reads overheating", "status": "unverified"}, {"name": "shutdown", "means": "the shutdown fires", "status": "unverified"}],
         "claim": "(overheat ->  shutdown)"}},
    {"kind": "everyday", "paper": "Modus ponens (Carroll's tortoise)",
     "ask_en": "The tortoise demands the rule itself be written as a premise: if (p implies q) and p, then q. True — but watch the completion table: it is a FRAME. A rule written down is certified, yet it moves nothing; a rule must be acted, not mailed.",
     "ask_ru": "Если p и «если p, то q», следует ли q? Черепаха Кэрролла.",
     "en": "Modus ponens (Carroll's tortoise)", "ru": "modus ponens (черепаха Кэрролла)",
     "doc": {
         "rows": [{"name": "p", "means": "the premise p holds", "status": "unverified"}, {"name": "q", "means": "the conclusion q holds", "status": "unverified"}],
         "claim": "(((p -> q) & p) -> q)"}},

    # -------------------------------------------------------------- audit
    {"kind": "audit",
     "ask_en": "An invoice line of 1500 against a ceiling of 5000 — does it fit?", "ask_ru": "Строка накладной на 1500 против потолка 5000 — влезает?",
     "en": "a line against its ceiling", "ru": "строка против потолка",
     "doc": {"rows": [
         {"name": "line", "means": "the invoice line", "status": "verified",
          "ground": "inv-17", "value": "1500", "unit": "RUB"},
         {"name": "budget", "means": "the ceiling", "status": "verified",
          "ground": "order-4", "value": "5000", "unit": "RUB"}],
         "claim": "line <= budget"}},
    {"kind": "audit",
     "ask_en": "Two lines resting on the same invoice — what falls if that invoice goes?", "ask_ru": "Две строки на одной накладной — что рухнет, если её снять?",
     "en": "two lines on ONE document — what falls together",
     "ru": "две строки на ОДНОМ документе — что падает вместе",
     "doc": {"rows": [
         {"name": "a", "means": "the first line", "status": "verified",
          "ground": "inv-17", "value": "100", "unit": "RUB"},
         {"name": "b", "means": "the second line", "status": "verified",
          "ground": "inv-17", "value": "200", "unit": "RUB"}],
         "claim": "a <= b"}},
    {"kind": "audit",
     "ask_en": "A fee backed by a certificate that expires, against what was paid.", "ask_ru": "Сбор по истекающему сертификату против того, что уплачено.",
     "en": "a warranty that expires", "ru": "гарантия, которая истекает",
     "doc": {"rows": [
         {"name": "fee", "means": "the fee under warranty",
          "status": "verified", "ground": "cert-7",
          "ground_kind": "certificate", "value": "100", "unit": "RUB"},
         {"name": "paid", "means": "what was paid", "status": "verified",
          "ground": "deed", "value": "80", "unit": "RUB"}],
         "claim": "paid <= fee"}},
    {"kind": "audit",
     "ask_en": "A figure we were quoted, against the agreed cap.", "ask_ru": "Названная нам цифра против оговорённого потолка.",
     "en": "an unverified figure in the sheet",
     "ru": "непроверенная цифра в листе",
     "doc": {"rows": [
         {"name": "quoted", "means": "the figure quoted to us",
          "status": "unverified", "value": "1200", "unit": "RUB"},
         {"name": "cap", "means": "the agreed cap", "status": "verified",
          "ground": "contract", "value": "1000", "unit": "RUB"}],
         "claim": "quoted <= cap"}},
    {"kind": "audit",
     "ask_en": "Is a fee of 5 roubles equal to an area of 3 square metres?", "ask_ru": "Равен ли сбор в 5 рублей площади в 3 квадратных метра?",
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
     "ask_en": "x minus 10 is 20 — what is x?", "ask_ru": "x минус 10 равно 20 — чему равен x?",
     "en": "solve for x", "ru": "найти x",
     "doc": {"rows": [
         {"name": "x", "means": "the unknown", "status": "unverified",
          "value": "?"}],
         "claim": "x - 10 = 20"}},
    {"kind": "numbers",
     "ask_en": "The total is 4500 and one line is 3000 — what is the other?", "ask_ru": "Итог 4500, одна строка 3000 — какова вторая?",
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
     "ask_en": "Masha has 2 sweets left; how many must she give Petya for them to be equal?", "ask_ru": "У Маши осталось 2 конфеты; сколько дать Пете, чтобы стало поровну?",
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
     "ask_en": "The age is between 11 and 13 — what is it?", "ask_ru": "Возраст между 11 и 13 — какой он?",
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
     "ask_en": "A third of 8, rounded to hundredths — what is it?", "ask_ru": "Треть от 8, округляемая до сотых — чему она равна?",
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
     "ask_en": "If it rains I take an umbrella. I have not checked the rain.", "ask_ru": "Если дождь — беру зонт. Дождь я не проверял.",
     "en": "if it rains I take an umbrella",
     "ru": "если дождь — беру зонт",
     "doc": {"rows": [
         {"name": "rain", "means": "it is raining", "status": "unverified"},
         {"name": "umbrella", "means": "I take an umbrella",
          "status": "unverified"}],
         "claim": "rain -> umbrella"}},
    {"kind": "everyday",
     "ask_en": "We ship once the invoice is paid. Payment is unverified.", "ask_ru": "Отгружаем, когда накладная оплачена. Оплата не проверена.",
     "en": "a promise on an unverified condition",
     "ru": "обещание на непроверенном условии",
     "doc": {"rows": [
         {"name": "paid", "means": "the invoice was paid",
          "status": "unverified"},
         {"name": "ship", "means": "we ship the goods",
          "status": "verified", "ground": "waybill-3"}],
         "claim": "paid -> ship"}},
    {"kind": "everyday",
     "ask_en": "The contract is signed; the goods have not been checked. Both?", "ask_ru": "Договор подписан, товар не проверен. Оба сразу?",
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
    items = [{"kind": e["kind"], "label": e.get(lang, e["en"]),
              # the question the example ANSWERS, so the chat shows what is
              # being asked rather than a verdict with no question above it
              "ask": e.get(f"ask_{lang}") or e.get("ask_en", ""),
              "doc": e["doc"]} for e in EXAMPLES]
    return {"kinds": kinds, "items": items}
