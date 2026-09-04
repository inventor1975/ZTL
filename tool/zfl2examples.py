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
    "paradox": {"en": "paradoxes and self-reference", "ru": "парадоксы и самоссылка", "uk": "парадокси й самопосилання", "he": "פרדוקסים והפניה עצמית", "de": "Paradoxien und Selbstbezug", "fr": "paradoxes et autoréférence", "es": "paradojas y autorreferencia"},
    "audit": {"en": "invoices and audit", "ru": "накладные и аудит", "uk": "накладні й аудит", "he": "חשבוניות וביקורת", "de": "Rechnungen und Prüfung", "fr": "factures et audit", "es": "facturas y auditoría"},
    "numbers": {"en": "asking for a number", "ru": "спросить число", "uk": "запитати число", "he": "לשאול מספר", "de": "nach einer Zahl fragen", "fr": "demander un nombre", "es": "pedir un número"},
    "clock": {"en": "the world's clock", "ru": "часы мира", "uk": "годинник світу", "he": "שעון העולם", "de": "die Uhr der Welt", "fr": "l'horloge du monde", "es": "el reloj del mundo"},
    "everyday": {"en": "everyday reasoning", "ru": "обычные рассуждения", "uk": "звичайні міркування", "he": "חשיבה יומיומית", "de": "alltägliches Schließen", "fr": "raisonnement ordinaire", "es": "razonamiento cotidiano"},
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
     "ask_uk": "Це речення хибне.",
     "ask_he": "המשפט הזה שקרי.",
     "ask_de": "Dieser Satz ist falsch.",
     "ask_fr": "Cette phrase est fausse.",
     "ask_es": "Esta oración es falsa.",
     "en": "Liar", "ru": "лжец",
     "uk": "брехун", "he": "השקרן", "de": "der Lügner", "fr": "le menteur", "es": "el mentiroso",
     "doc": {
         "rows": [{"name": "L", "means": "это предложение ложно", "status": "defined", "ground": "~(Tr(L))"}]}},
    {"kind": "paradox", "paper": "Barber (the liar in a barber's apron)",
     "ask_en": "The barber shaves exactly those who do not shave themselves. Does he shave himself?",
     "ask_ru": "Брадобрей бреет ровно тех, кто не бреется сам. Бреет ли он себя?",
     "ask_uk": "Цирульник голить рівно тих, хто не голиться сам. Чи голить він себе?",
     "ask_he": "הספר מגלח בדיוק את מי שאינם מגלחים את עצמם. האם הוא מגלח את עצמו?",
     "ask_de": "Der Barbier rasiert genau die, die sich nicht selbst rasieren. Rasiert er sich selbst?",
     "ask_fr": "Le barbier rase exactement ceux qui ne se rasent pas eux-mêmes. Se rase-t-il lui-même ?",
     "ask_es": "El barbero afeita exactamente a quienes no se afeitan a sí mismos. ¿Se afeita a sí mismo?",
     "en": "Barber (the liar in a barber's apron)", "ru": "брадобрей",
     "uk": "цирульник", "he": "הספר", "de": "der Barbier", "fr": "le barbier", "es": "el barbero",
     "doc": {
         "rows": [{"name": "shaves", "means": "брадобрей бреет самого себя", "status": "defined", "ground": "~(Tr(shaves))"}]}},
    {"kind": "paradox", "paper": "Grelling's 'heterological'",
     "ask_en": "'Heterological' means 'not applying to itself'. Is 'heterological' heterological?",
     "ask_ru": "«Гетерологичное» значит «неприменимое к себе». Гетерологично ли «гетерологичное»?",
     "ask_uk": "«Гетерологічне» означає «незастосовне до себе». Чи гетерологічне «гетерологічне»?",
     "ask_he": "«הטרולוגי» פירושו «שאינו חל על עצמו». האם «הטרולוגי» הוא הטרולוגי?",
     "ask_de": "„Heterologisch“ heißt „auf sich selbst nicht zutreffend“. Ist „heterologisch“ heterologisch?",
     "ask_fr": "« Hétérologique » signifie « ne s'appliquant pas à soi ». « Hétérologique » est-il hétérologique ?",
     "ask_es": "«Heterológico» significa «que no se aplica a sí mismo». ¿Es «heterológico» heterológico?",
     "en": "Grelling's 'heterological'", "ru": "«гетерологичное» Греллинга",
     "uk": "«гетерологічне» Ґреллінґа", "he": "«הטרולוגי» של גרלינג", "de": "Grellings „heterologisch“", "fr": "l'« hétérologique » de Grelling", "es": "el «heterológico» de Grelling",
     "doc": {
         "rows": [{"name": "het", "means": "«гетерологичное» не описывает само себя", "status": "defined", "ground": "~(Tr(het))"}]}},
    {"kind": "paradox", "paper": "Russell",
     "ask_en": "The set of all sets not containing themselves: does it contain itself? Universe: a = empty, b = {b}, R.",
     "ask_ru": "Множество всех множеств, не содержащих себя: содержит ли оно себя?",
     "ask_uk": "Множина всіх множин, що не містять себе: чи містить вона себе?",
     "ask_he": "קבוצת כל הקבוצות שאינן מכילות את עצמן: האם היא מכילה את עצמה?",
     "ask_de": "Die Menge aller Mengen, die sich nicht selbst enthalten: enthält sie sich selbst?",
     "ask_fr": "L'ensemble de tous les ensembles ne se contenant pas : se contient-il ?",
     "ask_es": "El conjunto de todos los conjuntos que no se contienen: ¿se contiene a sí mismo?",
     "en": "Russell", "ru": "Рассел",
     "uk": "Расселл", "he": "ראסל", "de": "Russell", "fr": "Russell", "es": "Russell",
     "doc": {
         "rows": [{"name": "a_in_a", "means": "a принадлежит a", "status": "refuted", "ground": "the-story"}, {"name": "a_in_b", "means": "a принадлежит b", "status": "refuted", "ground": "the-story"}, {"name": "a_in_R", "means": "a принадлежит R", "status": "defined", "ground": "~(Tr(a_in_a))"}, {"name": "b_in_a", "means": "b принадлежит a", "status": "refuted", "ground": "the-story"}, {"name": "b_in_b", "means": "b принадлежит b", "status": "verified", "ground": "the-story"}, {"name": "b_in_R", "means": "b принадлежит R", "status": "defined", "ground": "~(Tr(b_in_b))"}, {"name": "R_in_a", "means": "R принадлежит a", "status": "refuted", "ground": "the-story"}, {"name": "R_in_b", "means": "R принадлежит b", "status": "refuted", "ground": "the-story"}, {"name": "R_in_R", "means": "R принадлежит самому себе", "status": "defined", "ground": "~(Tr(R_in_R))"}]}},
    {"kind": "paradox", "paper": "Jourdain's postcard",
     "ask_en": "Front of the card: 'the sentence on the back is true'. Back: 'the sentence on the front is false'.",
     "ask_ru": "На одной стороне: «написанное на обороте — правда». На обороте: «написанное на лицевой — ложь».",
     "ask_uk": "З одного боку: «написане на звороті — правда». На звороті: «написане з лиця — хиба».",
     "ask_he": "בצד אחד: «מה שכתוב מאחור אמת». מאחור: «מה שכתוב מלפנים שקר».",
     "ask_de": "Vorn: „was hinten steht, ist wahr“. Hinten: „was vorn steht, ist falsch“.",
     "ask_fr": "Recto : « ce qui est au verso est vrai ». Verso : « ce qui est au recto est faux ».",
     "ask_es": "Anverso: «lo del reverso es verdad». Reverso: «lo del anverso es falso».",
     "en": "Jourdain's postcard", "ru": "открытка Жордена",
     "uk": "листівка Журдена", "he": "הגלויה של ז'ורדן", "de": "Jourdains Postkarte", "fr": "la carte postale de Jourdain", "es": "la postal de Jourdain",
     "doc": {
         "rows": [{"name": "front", "means": "написанное на обороте — правда", "status": "defined", "ground": "Tr(back)"}, {"name": "back", "means": "написанное на лицевой стороне — ложь", "status": "defined", "ground": "~(Tr(front))"}]}},
    {"kind": "paradox", "paper": "Crocodile",
     "ask_en": "The crocodile returns the child if and only if the mother guesses what he will do. The mother says: 'you will not return it'.",
     "ask_ru": "Крокодил возвращает ребёнка тогда и только тогда, когда мать угадала, что он сделает. Мать говорит: «не вернёшь».",
     "ask_uk": "Крокодил повертає дитину тоді й лише тоді, коли мати вгадала, що він зробить. Мати каже: «не повернеш».",
     "ask_he": "התנין מחזיר את הילד אם ורק אם האם ניחשה מה יעשה. האם אומרת: «לא תחזיר».",
     "ask_de": "Das Krokodil gibt das Kind genau dann zurück, wenn die Mutter errät, was es tun wird. Die Mutter sagt: „du gibst es nicht zurück“.",
     "ask_fr": "Le crocodile rend l'enfant si et seulement si la mère devine ce qu'il fera. La mère dit : « tu ne le rendras pas ».",
     "ask_es": "El cocodrilo devuelve al niño si y sólo si la madre adivina lo que hará. La madre dice: «no lo devolverás».",
     "en": "Crocodile", "ru": "крокодил",
     "uk": "крокодил", "he": "התנין", "de": "das Krokodil", "fr": "le crocodile", "es": "el cocodrilo",
     "doc": {
         "rows": [{"name": "R", "means": "крокодил возвращает ребёнка", "status": "defined", "ground": "Tr(M)"}, {"name": "M", "means": "мать угадала, что он сделает", "status": "defined", "ground": "~(Tr(R))"}]}},
    {"kind": "paradox", "paper": "Odd 3-cycle",
     "ask_en": "Three sentences in a ring, each denying the next.",
     "ask_ru": "Три предложения по кругу, каждое отрицает следующее.",
     "ask_uk": "Три речення по колу, кожне заперечує наступне.",
     "ask_he": "שלושה משפטים במעגל, כל אחד שולל את הבא.",
     "ask_de": "Drei Sätze im Kreis, jeder verneint den nächsten.",
     "ask_fr": "Trois phrases en cercle, chacune niant la suivante.",
     "ask_es": "Tres oraciones en círculo, cada una negando la siguiente.",
     "en": "Odd 3-cycle", "ru": "нечётный трёхцикл",
     "uk": "непарний трицикл", "he": "מעגל אי־זוגי בן 3", "de": "ungerader 3-Zyklus", "fr": "cycle impair de 3", "es": "ciclo impar de 3",
     "doc": {
         "rows": [{"name": "a", "means": "первое предложение цикла истинно", "status": "defined", "ground": "~(Tr(b))"}, {"name": "b", "means": "второе предложение цикла истинно", "status": "defined", "ground": "~(Tr(c))"}, {"name": "c", "means": "третье предложение цикла истинно", "status": "defined", "ground": "~(Tr(a))"}]}},
    {"kind": "paradox", "paper": "Curry (grounded falsum)",
     "ask_en": "'If this sentence is true, then the impossible holds', where the impossible is a sentence that has been refuted.",
     "ask_ru": "«Если это предложение истинно, то невозможное имеет место» — при настоящей лжи.",
     "ask_uk": "«Якщо це речення істинне, то неможливе має місце» — за справжньої хиби.",
     "ask_he": "«אם המשפט הזה אמיתי, אז מתקיים הבלתי אפשרי» — עם שקר ממשי.",
     "ask_de": "„Wenn dieser Satz wahr ist, dann gilt das Unmögliche“ — bei echtem Falsum.",
     "ask_fr": "« Si cette phrase est vraie, alors l'impossible a lieu » — avec un faux réel.",
     "ask_es": "«Si esta oración es verdadera, entonces ocurre lo imposible» — con un falso real.",
     "en": "Curry (grounded falsum)", "ru": "Карри (ложь настоящая)",
     "uk": "Каррі (хиба справжня)", "he": "קרי (שקר מבוסס)", "de": "Curry (echtes Falsum)", "fr": "Curry (faux fondé)", "es": "Curry (falso fundado)",
     "doc": {
         "rows": [{"name": "g", "means": "предложение Карри истинно", "status": "defined", "ground": "(Tr(g) ->  F)"}]}},
    {"kind": "paradox", "paper": "Curry (suspended falsum)",
     "ask_en": "Curry's sentence: if it is true, then the impossible holds. Here the 'impossible' is itself defined: it holds exactly when some sentence S is both true and false; and S is defined as 'S is true'.",
     "ask_ru": "Предложение Карри: если оно истинно, то имеет место невозможное. Здесь само «невозможное» определено: оно имеет место ровно тогда, когда некоторое предложение S и истинно, и ложно; а S определено как «S истинно».",
     "ask_uk": "Речення Каррі: якщо воно істинне, то має місце неможливе. Тут саме «неможливе» визначене: воно має місце саме тоді, коли деяке речення S і істинне, і хибне; а S визначене як «S істинне».",
     "ask_he": "משפט קרי: אם הוא אמיתי, אז הבלתי־אפשרי מתקיים. כאן «הבלתי־אפשרי» עצמו מוגדר: הוא מתקיים בדיוק כאשר משפט S הוא גם אמיתי וגם שקרי; ו-S מוגדר כ«S אמיתי».",
     "ask_de": "Currys Satz: wenn er wahr ist, dann gilt das Unmögliche. Hier ist das „Unmögliche“ selbst definiert: es gilt genau dann, wenn ein Satz S zugleich wahr und falsch ist; und S ist definiert als „S ist wahr“.",
     "ask_fr": "La phrase de Curry : si elle est vraie, alors l'impossible a lieu. Ici l'« impossible » est lui-même défini : il a lieu exactement quand une phrase S est à la fois vraie et fausse ; et S est définie comme « S est vraie ».",
     "ask_es": "La oración de Curry: si es verdadera, entonces lo imposible se da. Aquí lo «imposible» está definido: se da exactamente cuando alguna oración S es a la vez verdadera y falsa; y S se define como «S es verdadera».",
     "en": "Curry (suspended falsum)", "ru": "Карри (ложь подвешенная)",
     "uk": "Каррі (хиба підвішена)", "he": "קרי (שקר תלוי)", "de": "Curry (schwebendes Falsum)", "fr": "Curry (faux suspendu)", "es": "Curry (falso en suspenso)",
     "doc": {
         "rows": [{"name": "gamma", "means": "предложение Карри истинно", "status": "defined", "ground": "(Tr(gamma) ->  Tr(bot))"}, {"name": "bot", "means": "невозможное имеет место", "status": "defined", "ground": "(Tr(s) &  ~(Tr(s)))"}, {"name": "s", "means": "следствие Карри истинно", "status": "defined", "ground": "Tr(s)"}]}},
    {"kind": "paradox", "paper": "Strong liar (forced FALSE)",
     "ask_en": "'This sentence is false AND this sentence is true.'",
     "ask_ru": "«Это предложение ложно И это предложение истинно.»",
     "ask_uk": "«Це речення хибне І це речення істинне.»",
     "ask_he": "«המשפט הזה שקרי וגם המשפט הזה אמיתי.»",
     "ask_de": "„Dieser Satz ist falsch UND dieser Satz ist wahr.“",
     "ask_fr": "« Cette phrase est fausse ET cette phrase est vraie. »",
     "ask_es": "«Esta oración es falsa Y esta oración es verdadera.»",
     "en": "Strong liar (forced FALSE)", "ru": "усиленный лжец (вынужденно ЛОЖЬ)",
     "uk": "посилений брехун (вимушено ХИБА)", "he": "השקרן המחוזק (שקר בהכרח)", "de": "verstärkter Lügner (erzwungen FALSCH)", "fr": "menteur renforcé (FAUX forcé)", "es": "mentiroso reforzado (FALSO forzado)",
     "doc": {
         "rows": [{"name": "sigma", "means": "это предложение не истинно", "status": "defined", "ground": "(~(Tr(sigma)) &  Tr(sigma))"}]}},
    {"kind": "paradox", "paper": "Revenge / avenger (forced FALSE)",
     "ask_en": "'This sentence is not equivalent to itself.'",
     "ask_ru": "«Это предложение не равносильно самому себе.»",
     "ask_uk": "«Це речення не рівносильне самому собі.»",
     "ask_he": "«המשפט הזה אינו שקול לעצמו.»",
     "ask_de": "„Dieser Satz ist nicht äquivalent zu sich selbst.“",
     "ask_fr": "« Cette phrase n'est pas équivalente à elle-même. »",
     "ask_es": "«Esta oración no es equivalente a sí misma.»",
     "en": "Revenge / avenger (forced FALSE)", "ru": "мститель (вынужденно ЛОЖЬ)",
     "uk": "месник (вимушено ХИБА)", "he": "הנוקם (שקר בהכרח)", "de": "Rächer (erzwungen FALSCH)", "fr": "vengeur (FAUX forcé)", "es": "vengador (FALSO forzado)",
     "doc": {
         "rows": [{"name": "mu", "means": "это предложение не является заработанной истиной", "status": "defined", "ground": "not((Tr(mu) =  Tr(mu)))"}]}},
    {"kind": "paradox", "paper": "Henkin-style sentence (forced TRUE)",
     "ask_en": "'If this sentence is true, then this sentence is true.'",
     "ask_ru": "«Если это предложение истинно, то это предложение истинно.»",
     "ask_uk": "«Якщо це речення істинне, то це речення істинне.»",
     "ask_he": "«אם המשפט הזה אמיתי, אז המשפט הזה אמיתי.»",
     "ask_de": "„Wenn dieser Satz wahr ist, dann ist dieser Satz wahr.“",
     "ask_fr": "« Si cette phrase est vraie, alors cette phrase est vraie. »",
     "ask_es": "«Si esta oración es verdadera, entonces esta oración es verdadera.»",
     "en": "Henkin-style sentence (forced TRUE)", "ru": "предложение Хенкина (вынужденно ИСТИНА)",
     "uk": "речення Хенкіна (вимушено ІСТИНА)", "he": "משפט הנקין (אמת בהכרח)", "de": "Henkin-Satz (erzwungen WAHR)", "fr": "énoncé de Henkin (VRAI forcé)", "es": "enunciado de Henkin (VERDADERO forzado)",
     "doc": {
         "rows": [{"name": "h", "means": "это предложение доказуемо", "status": "defined", "ground": "(Tr(h) ->  Tr(h))"}]}},
    {"kind": "paradox", "paper": "Truth-teller",
     "ask_en": "This sentence is true.",
     "ask_ru": "«Это предложение истинно» — правдоруб.",
     "ask_uk": "«Це речення істинне» — правдомовець.",
     "ask_he": "«המשפט הזה אמיתי» — דובר האמת.",
     "ask_de": "„Dieser Satz ist wahr“ — der Wahrheitssager.",
     "ask_fr": "« Cette phrase est vraie » — le diseur de vérité.",
     "ask_es": "«Esta oración es verdadera» — el veraz.",
     "en": "Truth-teller", "ru": "правдоруб",
     "uk": "правдомовець", "he": "דובר האמת", "de": "der Wahrheitssager", "fr": "le diseur de vérité", "es": "el veraz",
     "doc": {
         "rows": [{"name": "tau", "means": "это предложение истинно", "status": "defined", "ground": "Tr(tau)"}]}},
    {"kind": "paradox", "paper": "Russell's twin S∈S",
     "ask_en": "The set of all sets that DO contain themselves: does it contain itself?",
     "ask_ru": "Множество, определённое как принадлежащее самому себе.",
     "ask_uk": "Множина, визначена як така, що належить сама собі.",
     "ask_he": "קבוצה המוגדרת ככזו השייכת לעצמה.",
     "ask_de": "Eine Menge, definiert als sich selbst enthaltend.",
     "ask_fr": "Un ensemble défini comme s'appartenant.",
     "ask_es": "Un conjunto definido como perteneciente a sí mismo.",
     "en": "Russell's twin S∈S", "ru": "близнец Рассела S∈S",
     "uk": "двійник Расселла S∈S", "he": "תאומו של ראסל S∈S", "de": "Russells Zwilling S∈S", "fr": "le jumeau de Russell S∈S", "es": "el gemelo de Russell S∈S",
     "doc": {
         "rows": [{"name": "S_in_S", "means": "множество S принадлежит самому себе", "status": "defined", "ground": "Tr(S_in_S)"}]}},
    {"kind": "paradox", "paper": "Crocodile control (optimistic mother)",
     "ask_en": "The same crocodile, but the mother says: 'you WILL return it'.",
     "ask_ru": "Тот же крокодил, но мать говорит: «вернёшь». Контроль.",
     "ask_uk": "Той самий крокодил, але мати каже: «повернеш». Контроль.",
     "ask_he": "אותו תנין, אבל האם אומרת: «תחזיר». בקרה.",
     "ask_de": "Dasselbe Krokodil, aber die Mutter sagt: „du gibst es zurück“. Kontrolle.",
     "ask_fr": "Le même crocodile, mais la mère dit : « tu le rendras ». Témoin.",
     "ask_es": "El mismo cocodrilo, pero la madre dice: «lo devolverás». Control.",
     "en": "Crocodile control (optimistic mother)", "ru": "крокодил, контроль (мать-оптимистка)",
     "uk": "крокодил, контроль (мати-оптимістка)", "he": "תנין, בקרה (אם אופטימית)", "de": "Krokodil, Kontrolle (optimistische Mutter)", "fr": "crocodile, témoin (mère optimiste)", "es": "cocodrilo, control (madre optimista)",
     "doc": {
         "rows": [{"name": "R", "means": "крокодил возвращает ребёнка", "status": "defined", "ground": "Tr(M)"}, {"name": "M", "means": "мать угадала, что он сделает", "status": "defined", "ground": "Tr(R)"}]}},
    {"kind": "paradox", "paper": "Even 2-cycle",
     "ask_en": "Two sentences, each denying the other.",
     "ask_ru": "Два предложения, каждое отрицает другое.",
     "ask_uk": "Два речення, кожне заперечує інше.",
     "ask_he": "שני משפטים, כל אחד שולל את השני.",
     "ask_de": "Zwei Sätze, jeder verneint den anderen.",
     "ask_fr": "Deux phrases, chacune niant l'autre.",
     "ask_es": "Dos oraciones, cada una negando a la otra.",
     "en": "Even 2-cycle", "ru": "чётный двуцикл",
     "uk": "парний двоцикл", "he": "מעגל זוגי בן 2", "de": "gerader 2-Zyklus", "fr": "cycle pair de 2", "es": "ciclo par de 2",
     "doc": {
         "rows": [{"name": "A", "means": "A истинно", "status": "defined", "ground": "~(Tr(B))"}, {"name": "B", "means": "B истинно", "status": "defined", "ground": "~(Tr(A))"}]}},
    {"kind": "paradox", "paper": "Even 4-cycle",
     "ask_en": "Four sentences in a ring, each denying the next.",
     "ask_ru": "Четыре предложения по кругу, чётное число отрицаний.",
     "ask_uk": "Чотири речення по колу, парне число заперечень.",
     "ask_he": "ארבעה משפטים במעגל, מספר זוגי של שלילות.",
     "ask_de": "Vier Sätze im Kreis, gerade Zahl von Verneinungen.",
     "ask_fr": "Quatre phrases en cercle, nombre pair de négations.",
     "ask_es": "Cuatro oraciones en círculo, número par de negaciones.",
     "en": "Even 4-cycle", "ru": "чётный четырёхцикл",
     "uk": "парний чотирицикл", "he": "מעגל זוגי בן 4", "de": "gerader 4-Zyklus", "fr": "cycle pair de 4", "es": "ciclo par de 4",
     "doc": {
         "rows": [{"name": "a", "means": "первое предложение цикла истинно", "status": "defined", "ground": "~(Tr(b))"}, {"name": "b", "means": "второе предложение цикла истинно", "status": "defined", "ground": "~(Tr(c))"}, {"name": "c", "means": "третье предложение цикла истинно", "status": "defined", "ground": "~(Tr(d))"}, {"name": "d", "means": "четвёртое предложение цикла истинно", "status": "defined", "ground": "~(Tr(a))"}]}},
    {"kind": "paradox", "paper": "Yablo (truncated at 3)",
     "ask_en": "Yablo, truncated at three: each sentence says that all the ones after it are false. The third has none after it, and is true for that reason.",
     "ask_ru": "Ябло, обрезанный до трёх: каждое предложение говорит, что все последующие ложны. У третьего последующих нет, и потому оно истинно.",
     "ask_uk": "Ябло, обрізаний до трьох: кожне речення каже, що всі наступні хибні. У третього наступних немає, і тому воно істинне.",
     "ask_he": "יאבלו, קטוע בשלושה: כל משפט אומר שכל הבאים אחריו שקריים. לשלישי אין באים אחריו, ולכן הוא אמיתי.",
     "ask_de": "Yablo, bei drei abgeschnitten: jeder Satz sagt, dass alle nachfolgenden falsch sind. Der dritte hat keine nachfolgenden und ist deshalb wahr.",
     "ask_fr": "Yablo, tronqué à trois : chaque phrase dit que toutes les suivantes sont fausses. La troisième n'en a aucune après elle, et elle est vraie pour cette raison.",
     "ask_es": "Yablo, truncado en tres: cada oración dice que todas las siguientes son falsas. La tercera no tiene ninguna después, y por eso es verdadera.",
     "en": "Yablo (truncated at 3)", "ru": "Ябло (обрезанный до 3)",
     "uk": "Ябло (обрізаний до 3)", "he": "יבלו (מקוצר ל־3)", "de": "Yablo (auf 3 gekürzt)", "fr": "Yablo (tronqué à 3)", "es": "Yablo (truncado a 3)",
     "doc": {
         "rows": [{"name": "s0", "means": "ни одно из последующих не истинно", "status": "defined", "ground": "(~(Tr(s1)) &  ~(Tr(s2)))"}, {"name": "s1", "means": "ни одно из последующих не истинно", "status": "defined", "ground": "~(Tr(s2))"}, {"name": "s2", "means": "ни одно из последующих не истинно", "status": "verified", "ground": "the-story"}]}},
    {"kind": "paradox", "paper": "Contingent liar — world A (harmless)",
     "ask_en": "Smith says: 'what Jones said is false'. Jones said something true about grass, and that it is true has been established.",
     "ask_ru": "Смит говорит «Джонс лжёт», Джонс говорит правду о траве. Мир, где всё безобидно.",
     "ask_uk": "Сміт каже «Джонс бреше», Джонс каже правду про траву. Світ, де все безневинно.",
     "ask_he": "סמית אומר «ג'ונס משקר», ג'ונס אומר אמת על הדשא. עולם שבו הכול לא מזיק.",
     "ask_de": "Smith sagt „Jones lügt“, Jones sagt etwas Wahres über das Gras. Eine harmlose Welt.",
     "ask_fr": "Smith dit « Jones ment », Jones dit vrai sur l'herbe. Un monde inoffensif.",
     "ask_es": "Smith dice «Jones miente», Jones dice algo verdadero sobre la hierba. Un mundo inofensivo.",
     "en": "Contingent liar — world A (harmless)", "ru": "контингентный лжец — мир A (безобидный)",
     "uk": "контингентний брехун — світ A (безневинний)", "he": "שקרן מותנה — עולם A (לא מזיק)", "de": "kontingenter Lügner — Welt A (harmlos)", "fr": "menteur contingent — monde A (inoffensif)", "es": "mentiroso contingente — mundo A (inofensivo)",
     "doc": {
         "rows": [{"name": "S", "means": "сказанное Смитом истинно", "status": "defined", "ground": "~(Tr(J))"}, {"name": "J", "means": "сказанное Джонсом истинно", "status": "defined", "ground": "Tr(g)"}, {"name": "g", "means": "предложение Карри истинно", "status": "verified", "ground": "the-story"}]}},
    {"kind": "paradox", "paper": "Contingent liar — world B (unlucky)",
     "ask_en": "The same Smith sentence, but Jones said: 'what Smith said is true'.",
     "ask_ru": "Тот же Смит, но Джонс говорит «Смит прав». Круг замкнулся.",
     "ask_uk": "Той самий Сміт, але Джонс каже «Сміт має рацію». Коло замкнулося.",
     "ask_he": "אותו סמית, אבל ג'ונס אומר «סמית צודק». המעגל נסגר.",
     "ask_de": "Derselbe Smith, aber Jones sagt „Smith hat recht“. Der Kreis schließt sich.",
     "ask_fr": "Le même Smith, mais Jones dit « Smith a raison ». La boucle se referme.",
     "ask_es": "El mismo Smith, pero Jones dice «Smith tiene razón». El círculo se cierra.",
     "en": "Contingent liar — world B (unlucky)", "ru": "контингентный лжец — мир B (неудачный)",
     "uk": "контингентний брехун — світ B (невдалий)", "he": "שקרן מותנה — עולם B (ביש מזל)", "de": "kontingenter Lügner — Welt B (unglücklich)", "fr": "menteur contingent — monde B (malchanceux)", "es": "mentiroso contingente — mundo B (desafortunado)",
     "doc": {
         "rows": [{"name": "S", "means": "сказанное Смитом истинно", "status": "defined", "ground": "~(Tr(J))"}, {"name": "J", "means": "сказанное Джонсом истинно", "status": "defined", "ground": "Tr(S)"}]}},
    {"kind": "paradox", "paper": "Contingent liar — world C (unverified)",
     "ask_en": "The same Smith sentence; what Jones said has not been verified.",
     "ask_ru": "Тот же Смит, но что сказал Джонс — неизвестно.",
     "ask_uk": "Той самий Сміт, але що сказав Джонс — невідомо.",
     "ask_he": "אותו סמית, אבל מה שג'ונס אמר אינו ידוע.",
     "ask_de": "Derselbe Smith, aber was Jones sagte, ist unbekannt.",
     "ask_fr": "Le même Smith, mais ce qu'a dit Jones est inconnu.",
     "ask_es": "El mismo Smith, pero lo que dijo Jones se desconoce.",
     "en": "Contingent liar — world C (unverified)", "ru": "контингентный лжец — мир C (непроверенный)",
     "uk": "контингентний брехун — світ C (неперевірений)", "he": "שקרן מותנה — עולם C (לא אומת)", "de": "kontingenter Lügner — Welt C (ungeprüft)", "fr": "menteur contingent — monde C (non vérifié)", "es": "mentiroso contingente — mundo C (sin verificar)",
     "doc": {
         "rows": [{"name": "J", "means": "what Jones said is true", "status": "unverified"}, {"name": "S", "means": "сказанное Смитом истинно", "status": "defined", "ground": "~(Tr(J))"}]}},
    {"kind": "paradox", "paper": "Ship of Theseus: the title contest",
     "ask_en": "Repaired ship A and reassembled ship B each claim the title 'the real one': A holds it exactly when B does not, and B holds it exactly when A does not.",
     "ask_ru": "Починенный корабль A и пересобранный корабль B спорят за титул «тот самый»: A носит его ровно тогда, когда его не носит B, и B носит его ровно тогда, когда его не носит A.",
     "ask_uk": "Полагоджений корабель A і зібраний наново корабель B змагаються за титул «той самий»: A носить його саме тоді, коли його не носить B, і B носить його саме тоді, коли його не носить A.",
     "ask_he": "הספינה המתוקנת A והספינה המורכבת מחדש B מתחרות על התואר «האמיתית»: A נושאת אותו בדיוק כאשר B אינה נושאת, ו-B נושאת אותו בדיוק כאשר A אינה נושאת.",
     "ask_de": "Das reparierte Schiff A und das wieder zusammengesetzte Schiff B streiten um den Titel „das eigentliche“: A trägt ihn genau dann, wenn B ihn nicht trägt, und B genau dann, wenn A ihn nicht trägt.",
     "ask_fr": "Le navire réparé A et le navire réassemblé B se disputent le titre « le vrai » : A le porte exactement quand B ne le porte pas, et B exactement quand A ne le porte pas.",
     "ask_es": "El barco reparado A y el barco reensamblado B disputan el título «el verdadero»: A lo lleva exactamente cuando B no lo lleva, y B exactamente cuando A no lo lleva.",
     "en": "Ship of Theseus: the title contest", "ru": "Корабль Тесея: спор о титуле",
     "uk": "Корабель Тесея: спір про титул", "he": "ספינת תזאוס: הריב על התואר", "de": "Schiff des Theseus: der Titelstreit", "fr": "le navire de Thésée : la dispute du titre", "es": "la nave de Teseo: la disputa del título",
     "doc": {
         "rows": [{"name": "theA", "means": "титул принадлежит кораблю A", "status": "defined", "ground": "~(Tr(theB))"}, {"name": "theB", "means": "титул принадлежит кораблю B", "status": "defined", "ground": "~(Tr(theA))"}]}},
    {"kind": "paradox", "paper": "Agrippa's dogma (foundation with a passport)",
     "ask_en": "A claim stands on a foundation, and the foundation is defined as holding exactly when it itself holds.",
     "ask_ru": "Утверждение стоит на фундаменте, который держится сам собой.",
     "ask_uk": "Твердження стоїть на фундаменті, що тримається сам собою.",
     "ask_he": "טענה עומדת על יסוד שנתמך בעצמו.",
     "ask_de": "Eine Behauptung steht auf einem Fundament, das sich selbst trägt.",
     "ask_fr": "Une affirmation repose sur un fondement qui se soutient lui-même.",
     "ask_es": "Una afirmación se apoya en un fundamento que se sostiene solo.",
     "en": "Agrippa's dogma (foundation with a passport)", "ru": "догма Агриппы (основание с паспортом)",
     "uk": "догма Агріппи (підстава з паспортом)", "he": "הדוגמה של אגריפה (יסוד עם דרכון)", "de": "Agrippas Dogma (Fundament mit Pass)", "fr": "le dogme d'Agrippa (fondement avec passeport)", "es": "el dogma de Agripa (fundamento con pasaporte)",
     "doc": {
         "rows": [{"name": "p", "means": "утверждение, стоящее на фундаменте", "status": "defined", "ground": "Tr(f)"}, {"name": "f", "means": "фундамент держится сам собой", "status": "defined", "ground": "Tr(f)"}]}},
    {"kind": "paradox", "paper": "Same person? (corecursion, all observations match)",
     "ask_en": "'The same person' holds exactly when the observations match and it goes on holding. Every observation made so far matches.",
     "ask_ru": "Тот же ли это человек, если все наблюдения совпадают?",
     "ask_uk": "Чи та сама це людина, якщо всі спостереження збігаються?",
     "ask_he": "האם זה אותו אדם, אם כל התצפיות תואמות?",
     "ask_de": "Ist es dieselbe Person, wenn alle Beobachtungen übereinstimmen?",
     "ask_fr": "Est-ce la même personne si toutes les observations concordent ?",
     "ask_es": "¿Es la misma persona si todas las observaciones coinciden?",
     "en": "Same person? (corecursion, all observations match)", "ru": "тот же человек? (корекурсия)",
     "uk": "та сама людина? (корекурсія)", "he": "אותו אדם? (קורקורסיה)", "de": "dieselbe Person? (Korekursion)", "fr": "la même personne ? (corécursion)", "es": "¿la misma persona? (corecursión)",
     "doc": {
         "rows": [{"name": "obs", "means": "every observation so far matches", "status": "verified", "ground": "the-story"}, {"name": "S", "means": "сказанное Смитом истинно", "status": "defined", "ground": "(Tr(obs) &  Tr(S))"}]}},
    {"kind": "everyday", "paper": "Sensor",
     "ask_en": "An unverified sensor reports overheating; if overheating, the shutdown fires. Will it fire? (Also try the one-line human syntax: assert overheat impl shutdown)",
     "ask_ru": "Датчик показывает перегрев — должно ли сработать отключение?",
     "ask_uk": "Датчик показує перегрів — чи має спрацювати вимкнення?",
     "ask_he": "החיישן מראה התחממות יתר — האם הכיבוי אמור לפעול?",
     "ask_de": "Der Sensor meldet Überhitzung — soll die Abschaltung greifen?",
     "ask_fr": "Le capteur signale une surchauffe — l'arrêt doit-il se déclencher ?",
     "ask_es": "El sensor indica sobrecalentamiento — ¿debe activarse el apagado?",
     "en": "Sensor", "ru": "датчик",
     "uk": "датчик", "he": "חיישן", "de": "Sensor", "fr": "capteur", "es": "sensor",
     "doc": {
         "rows": [{"name": "overheat", "means": "the sensor reads overheating", "status": "unverified"}, {"name": "shutdown", "means": "the shutdown fires", "status": "unverified"}],
         "claim": "(overheat ->  shutdown)"}},
    {"kind": "everyday", "paper": "Modus ponens (Carroll's tortoise)",
     "ask_en": "The tortoise demands the rule itself be written as a premise: if (p implies q) and p, then q. True — but watch the completion table: it is a FRAME. A rule written down is certified, yet it moves nothing; a rule must be acted, not mailed.",
     "ask_ru": "Если p и «если p, то q», следует ли q? Черепаха Кэрролла.",
     "ask_uk": "Якщо p і «якщо p, то q», чи випливає q? Черепаха Керролла.",
     "ask_he": "אם p וגם «אם p אז q», האם נובע q? הצב של קרול.",
     "ask_de": "Wenn p und „wenn p, dann q“ — folgt q? Carrolls Schildkröte.",
     "ask_fr": "Si p et « si p alors q », q suit-il ? La tortue de Carroll.",
     "ask_es": "Si p y «si p entonces q», ¿se sigue q? La tortuga de Carroll.",
     "en": "Modus ponens (Carroll's tortoise)", "ru": "modus ponens (черепаха Кэрролла)",
     "uk": "modus ponens (черепаха Керролла)", "he": "מודוס פוננס (הצב של קרול)", "de": "Modus ponens (Carrolls Schildkröte)", "fr": "modus ponens (la tortue de Carroll)", "es": "modus ponens (la tortuga de Carroll)",
     "doc": {
         "rows": [{"name": "p", "means": "the premise p holds", "status": "unverified"}, {"name": "q", "means": "the conclusion q holds", "status": "unverified"}],
         "claim": "(((p -> q) & p) -> q)"}},

    # -------------------------------------------------------------- audit
    {"kind": "audit",
     "ask_en": "An invoice line of 1500 against a ceiling of 5000 — does it fit?", "ask_ru": "Строка накладной на 1500 против потолка 5000 — влезает?",
     "ask_uk": "Рядок накладної на 1500 проти стелі 5000 — вміщається?",
     "ask_he": "שורת חשבונית של 1500 מול תקרה של 5000 — נכנסת?",
     "ask_de": "Eine Rechnungszeile über 1500 gegen eine Obergrenze von 5000 — passt sie?",
     "ask_fr": "Une ligne de facture de 1500 face à un plafond de 5000 — passe-t-elle ?",
     "ask_es": "Una línea de factura de 1500 frente a un tope de 5000 — ¿cabe?",
     "en": "a line against its ceiling", "ru": "строка против потолка",
     "uk": "рядок проти стелі", "he": "שורה מול התקרה", "de": "eine Zeile gegen ihre Obergrenze", "fr": "une ligne face à son plafond", "es": "una línea contra su tope",
     "doc": {"rows": [
         {"name": "line", "means": "the invoice line", "status": "verified",
          "ground": "inv-17", "value": "1500", "unit": "RUB"},
         {"name": "budget", "means": "the ceiling", "status": "verified",
          "ground": "order-4", "value": "5000", "unit": "RUB"}],
         "claim": "line <= budget"}},
    {"kind": "audit",
     "ask_en": "Two lines resting on the same invoice — what falls if that invoice goes?", "ask_ru": "Две строки на одной накладной — что рухнет, если её снять?",
     "ask_uk": "Два рядки на одній накладній — що впаде, якщо її зняти?",
     "ask_he": "שתי שורות על אותה חשבונית — מה ייפול אם היא תוסר?",
     "ask_de": "Zwei Zeilen auf einer Rechnung — was fällt, wenn sie wegfällt?",
     "ask_fr": "Deux lignes sur une même facture — que tombe-t-il si on la retire ?",
     "ask_es": "Dos líneas en una misma factura — ¿qué cae si se retira?",
     "en": "two lines on ONE document — what falls together",
     "ru": "две строки на ОДНОМ документе — что падает вместе",
     "uk": "два рядки на ОДНОМУ документі — що падає разом", "he": "שתי שורות על מסמך אחד — מה נופל יחד", "de": "zwei Zeilen auf EINEM Dokument — was zusammen fällt", "fr": "deux lignes sur UN document — ce qui tombe ensemble", "es": "dos líneas en UN documento — qué cae junto",
     "doc": {"rows": [
         {"name": "a", "means": "the first line", "status": "verified",
          "ground": "inv-17", "value": "100", "unit": "RUB"},
         {"name": "b", "means": "the second line", "status": "verified",
          "ground": "inv-17", "value": "200", "unit": "RUB"}],
         "claim": "a <= b"}},
    {"kind": "audit",
     "ask_en": "A fee backed by a certificate that expires, against what was paid.", "ask_ru": "Сбор по истекающему сертификату против того, что уплачено.",
     "ask_uk": "Збір за сертифікатом, що спливає, проти сплаченого.",
     "ask_he": "אגרה על סמך אישור שפג תוקפו מול מה ששולם.",
     "ask_de": "Eine Gebühr auf einem ablaufenden Zertifikat gegen das Gezahlte.",
     "ask_fr": "Une redevance sur un certificat qui expire face à ce qui fut payé.",
     "ask_es": "Una tasa sobre un certificado que caduca frente a lo pagado.",
     "en": "a warranty that expires", "ru": "гарантия, которая истекает",
     "uk": "гарантія, що спливає", "he": "ערובה שפגה", "de": "eine Gewähr, die abläuft", "fr": "une garantie qui expire", "es": "una garantía que caduca",
     "doc": {"rows": [
         {"name": "fee", "means": "the fee under warranty",
          "status": "verified", "ground": "cert-7",
          "ground_kind": "certificate", "value": "100", "unit": "RUB"},
         {"name": "paid", "means": "what was paid", "status": "verified",
          "ground": "deed", "value": "80", "unit": "RUB"}],
         "claim": "paid <= fee"}},
    {"kind": "audit",
     "ask_en": "A figure we were quoted, against the agreed cap.", "ask_ru": "Названная нам цифра против оговорённого потолка.",
     "ask_uk": "Названа нам цифра проти обумовленої стелі.",
     "ask_he": "מספר שנמסר לנו מול התקרה שסוכמה.",
     "ask_de": "Eine uns genannte Zahl gegen die vereinbarte Obergrenze.",
     "ask_fr": "Un chiffre qu'on nous a donné face au plafond convenu.",
     "ask_es": "Una cifra que nos dieron frente al tope acordado.",
     "en": "an unverified figure in the sheet",
     "ru": "непроверенная цифра в листе",
     "uk": "неперевірена цифра в аркуші", "he": "מספר לא מאומת בגיליון", "de": "eine ungeprüfte Zahl im Blatt", "fr": "un chiffre non vérifié dans la feuille", "es": "una cifra sin verificar en la hoja",
     "doc": {"rows": [
         {"name": "quoted", "means": "the figure quoted to us",
          "status": "unverified", "value": "1200", "unit": "RUB"},
         {"name": "cap", "means": "the agreed cap", "status": "verified",
          "ground": "contract", "value": "1000", "unit": "RUB"}],
         "claim": "quoted <= cap"}},
    {"kind": "audit",
     "ask_en": "Is a fee of 5 roubles equal to an area of 3 square metres?", "ask_ru": "Равен ли сбор в 5 рублей площади в 3 квадратных метра?",
     "ask_uk": "Чи дорівнює збір у 5 гривень площі в 3 квадратні метри?",
     "ask_he": "האם אגרה של 5 שקלים שווה לשטח של 3 מטרים רבועים?",
     "ask_de": "Sind 5 Euro Gebühr gleich einer Fläche von 3 Quadratmetern?",
     "ask_fr": "Une redevance de 5 euros égale-t-elle une aire de 3 mètres carrés ?",
     "ask_es": "¿Una tasa de 5 euros es igual a un área de 3 metros cuadrados?",
     "en": "metres against roubles — the fourth corner",
     "ru": "метры против рублей — четвёртый угол",
     "uk": "метри проти гривень — четвертий кут", "he": "מטרים מול שקלים — הפינה הרביעית", "de": "Meter gegen Euro — die vierte Ecke", "fr": "mètres contre euros — le quatrième coin", "es": "metros contra euros — la cuarta esquina",
     "doc": {"rows": [
         {"name": "area", "means": "the area", "status": "verified",
          "ground": "plan", "value": "3", "unit": "m2"},
         {"name": "fee", "means": "the fee", "status": "verified",
          "ground": "reg-7", "value": "5", "unit": "RUB"}],
         "claim": "fee == area"}},

    # ------------------------------------------------------------ numbers
    {"kind": "numbers",
     "ask_en": "x minus 10 is 20 — what is x?", "ask_ru": "x минус 10 равно 20 — чему равен x?",
     "ask_uk": "x мінус 10 дорівнює 20 — чому дорівнює x?",
     "ask_he": "x פחות 10 שווה 20 — כמה שווה x?",
     "ask_de": "x minus 10 ist 20 — was ist x?",
     "ask_fr": "x moins 10 égale 20 — que vaut x ?",
     "ask_es": "x menos 10 es 20 — ¿cuánto vale x?",
     "en": "solve for x", "ru": "найти x",
     "uk": "знайти x", "he": "למצוא את x", "de": "x bestimmen", "fr": "trouver x", "es": "hallar x",
     "doc": {"rows": [
         {"name": "x", "means": "the unknown", "status": "unverified",
          "value": "?"}],
         "claim": "x - 10 = 20"}},
    {"kind": "numbers",
     "ask_en": "The total is 4500 and one line is 3000 — what is the other?", "ask_ru": "Итог 4500, одна строка 3000 — какова вторая?",
     "ask_uk": "Підсумок 4500, один рядок 3000 — який другий?",
     "ask_he": "הסכום 4500, שורה אחת 3000 — מהי השנייה?",
     "ask_de": "Die Summe ist 4500, eine Zeile 3000 — wie hoch ist die andere?",
     "ask_fr": "Le total est 4500, une ligne 3000 — quelle est l'autre ?",
     "ask_es": "El total es 4500, una línea 3000 — ¿cuál es la otra?",
     "en": "the missing line of an invoice",
     "ru": "недостающая строка накладной",
     "uk": "рядок накладної, якого бракує", "he": "השורה החסרה בחשבונית", "de": "die fehlende Zeile einer Rechnung", "fr": "la ligne manquante d'une facture", "es": "la línea que falta en una factura",
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
     "ask_uk": "У Маші лишилося 2 цукерки; скільки дати Петрові, щоб стало порівну?",
     "ask_he": "למאשה נשארו 2 סוכריות; כמה לתת לפטיה כדי שיהיה שווה?",
     "ask_de": "Mascha hat noch 2 Bonbons; wie viele muss sie Petja geben, damit es gleich ist?",
     "ask_fr": "Macha a 2 bonbons ; combien en donner à Petia pour que ce soit égal ?",
     "ask_es": "A Masha le quedan 2 caramelos; ¿cuántos darle a Petia para que sea igual?",
     "en": "a school word problem, in candies",
     "ru": "школьная задача, в конфетах",
     "uk": "шкільна задача, в цукерках", "he": "תרגיל בית ספר, בסוכריות", "de": "eine Schulaufgabe, in Bonbons", "fr": "un problème d'école, en bonbons", "es": "un problema escolar, en caramelos",
     "doc": {"rows": [
         {"name": "masha", "means": "what Masha has left after Vasya",
          "status": "verified", "ground": "the-story", "value": "2",
          "unit": "candies"},
         {"name": "give", "means": "how many she gives Petya",
          "status": "unverified", "value": "?", "unit": "candies"}],
         "claim": "masha - give = give"}},
    {"kind": "numbers",
     "ask_en": "The age is between 11 and 13 — what is it?", "ask_ru": "Возраст между 11 и 13 — какой он?",
     "ask_uk": "Вік між 11 і 13 — який він?",
     "ask_he": "הגיל בין 11 ל־13 — מהו?",
     "ask_de": "Das Alter liegt zwischen 11 und 13 — wie hoch ist es?",
     "ask_fr": "L'âge est entre 11 et 13 — quel est-il ?",
     "ask_es": "La edad está entre 11 y 13 — ¿cuál es?",
     "en": "a box that stays a box", "ru": "коробка, которая остаётся коробкой",
     "uk": "коробка, що лишається коробкою", "he": "קופסה שנשארת קופסה", "de": "eine Schachtel, die eine Schachtel bleibt", "fr": "une boîte qui reste une boîte", "es": "una caja que sigue siendo caja",
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
     "ask_uk": "Третина від 8, округлена до сотих — чому вона дорівнює?",
     "ask_he": "שליש מ־8, מעוגל למאיות — כמה זה?",
     "ask_de": "Ein Drittel von 8, auf Hundertstel gerundet — wie viel ist das?",
     "ask_fr": "Un tiers de 8, arrondi au centième — combien vaut-il ?",
     "ask_es": "Un tercio de 8, redondeado a centésimas — ¿cuánto es?",
     "en": "a third that no scale of hundredths holds",
     "ru": "треть, которой не вмещают сотые",
     "uk": "третина, якої не вміщають соті", "he": "שליש שהמאיות אינן מכילות", "de": "ein Drittel, das keine Hundertstel fassen", "fr": "un tiers qu'aucun centième ne contient", "es": "un tercio que las centésimas no contienen",
     "doc": {"rows": [
         {"name": "share", "means": "one third of the whole",
          "status": "unverified", "value": "?", "scale": "decimal2"},
         {"name": "whole", "means": "the whole", "status": "verified",
          "ground": "deed", "value": "8"}],
         "claim": "share * 3 = whole"}},

    # ----------------------------------------------------------- everyday
    {"kind": "everyday",
     "ask_en": "If it rains I take an umbrella. I have not checked the rain.", "ask_ru": "Если дождь — беру зонт. Дождь я не проверял.",
     "ask_uk": "Якщо дощ — беру парасольку. Дощ я не перевіряв.",
     "ask_he": "אם יורד גשם — אני לוקח מטרייה. את הגשם לא בדקתי.",
     "ask_de": "Wenn es regnet, nehme ich einen Schirm. Den Regen habe ich nicht geprüft.",
     "ask_fr": "S'il pleut, je prends un parapluie. Je n'ai pas vérifié la pluie.",
     "ask_es": "Si llueve, cojo un paraguas. No he comprobado la lluvia.",
     "en": "if it rains I take an umbrella",
     "ru": "если дождь — беру зонт",
     "uk": "якщо дощ — беру парасольку", "he": "אם יורד גשם — אני לוקח מטרייה", "de": "wenn es regnet, nehme ich einen Schirm", "fr": "s'il pleut, je prends un parapluie", "es": "si llueve, cojo un paraguas",
     "doc": {"rows": [
         {"name": "rain", "means": "it is raining", "status": "unverified"},
         {"name": "umbrella", "means": "I take an umbrella",
          "status": "unverified"}],
         "claim": "rain -> umbrella"}},
    {"kind": "everyday",
     "ask_en": "We ship once the invoice is paid. Payment is unverified.", "ask_ru": "Отгружаем, когда накладная оплачена. Оплата не проверена.",
     "ask_uk": "Відвантажуємо, коли накладну оплачено. Оплату не перевірено.",
     "ask_he": "נשלח כשהחשבונית שולמה. התשלום לא אומת.",
     "ask_de": "Wir liefern, sobald die Rechnung bezahlt ist. Die Zahlung ist ungeprüft.",
     "ask_fr": "Nous expédions une fois la facture payée. Le paiement n'est pas vérifié.",
     "ask_es": "Enviamos cuando la factura esté pagada. El pago no está verificado.",
     "en": "a promise on an unverified condition",
     "ru": "обещание на непроверенном условии",
     "uk": "обіцянка на неперевіреній умові", "he": "הבטחה על תנאי שלא אומת", "de": "ein Versprechen auf ungeprüfter Bedingung", "fr": "une promesse sur condition non vérifiée", "es": "una promesa sobre condición sin verificar",
     "doc": {"rows": [
         {"name": "paid", "means": "the invoice was paid",
          "status": "unverified"},
         {"name": "ship", "means": "we ship the goods",
          "status": "verified", "ground": "waybill-3"}],
         "claim": "paid -> ship"}},
    {"kind": "everyday",
     "ask_en": "The contract is signed; the goods have not been checked. Both?", "ask_ru": "Договор подписан, товар не проверен. Оба сразу?",
     "ask_uk": "Договір підписано, товар не перевірено. Обидва одразу?",
     "ask_he": "החוזה נחתם, הסחורה לא נבדקה. שניהם יחד?",
     "ask_de": "Der Vertrag ist unterschrieben, die Ware ungeprüft. Beides zugleich?",
     "ask_fr": "Le contrat est signé, la marchandise non vérifiée. Les deux à la fois ?",
     "ask_es": "El contrato está firmado, la mercancía sin revisar. ¿Ambos a la vez?",
     "en": "what one verification buys", "ru": "что покупает одна проверка",
     "uk": "що купує одна перевірка", "he": "מה קונה אימות אחד", "de": "was eine Prüfung einbringt", "fr": "ce qu'achète une vérification", "es": "qué compra una verificación",
     "doc": {"rows": [
         {"name": "signed", "means": "the contract is signed",
          "status": "verified", "ground": "scan-12"},
         {"name": "delivered", "means": "the goods arrived",
          "status": "unverified"}],
         "claim": "signed & delivered"}},
    # ------------------------------------ the world's clock (expires_on)
    # The column exists and the floor computes, but nothing in the
    # catalogue reached them — a capability nobody can stumble upon is a
    # capability nobody has. Both cases are the same shape as E25's own
    # witnesses: a conclusion standing on ground that a dated event takes
    # back.
    {"kind": "clock",
     "ask_en": "The pledge registry gets re-read. Does the deal still stand?",
     "ask_ru": "Реестр залогов перечитывают. Сделка ещё стоит?",
     "ask_uk": "Реєстр застав перечитують. Угода ще стоїть?",
     "ask_he": "מרשם השעבודים נקרא מחדש. האם העסקה עדיין עומדת?",
     "ask_de": "Das Pfandregister wird neu gelesen. Steht der Kauf noch?",
     "ask_fr": "Le registre des gages est relu. L'affaire tient-elle encore ?",
     "ask_es": "El registro de prendas se vuelve a leer. ¿Sigue en pie el trato?",
     "en": "A purchase and a registry that is re-read",
     "ru": "покупка и реестр, который перечитают",
     "uk": "купівля і реєстр, який перечитають",
     "he": "רכישה ומרשם שייקרא מחדש",
     "de": "ein Kauf und ein Register, das neu gelesen wird",
     "fr": "un achat et un registre que l'on relit",
     "es": "una compra y un registro que se relee",
     "doc": {"rows": [
         {"name": "registry_recheck", "means": "реестр залогов перечитывают",
          "status": "unverified", "ground": ""},
         {"name": "pledge_free", "means": "машина не в залоге",
          "status": "verified", "ground": "vypiska",
          "expires_on": "registry_recheck"},
         {"name": "papers_ok", "means": "документы в порядке",
          "status": "verified", "ground": "pts"},
         {"name": "deal_ok", "means": "сделку можно закрывать",
          "status": "defined", "ground": "Tr(pledge_free) & Tr(papers_ok)"}],
         "claim": "deal_ok"}},
    {"kind": "clock",
     "ask_en": "The certificate comes up for renewal. What happens to the conclusion resting on it?",
     "ask_ru": "Сертификат выходит на продление. Что станет с выводом, который на нём стоит?",
     "ask_uk": "Сертифікат виходить на продовження. Що буде з висновком, який на ньому стоїть?",
     "ask_he": "התעודה עומדת לחידוש. מה יקרה למסקנה הנשענת עליה?",
     "ask_de": "Das Zertifikat steht zur Verlängerung an. Was wird aus dem Schluss, der darauf ruht?",
     "ask_fr": "Le certificat arrive à renouvellement. Qu'advient-il de la conclusion qui s'y appuie ?",
     "ask_es": "El certificado llega a renovación. ¿Qué pasa con la conclusión que se apoya en él?",
     "en": "A certificate up for renewal",
     "ru": "сертификат на продлении",
     "uk": "сертифікат на продовженні",
     "he": "תעודה לקראת חידוש",
     "de": "ein Zertifikat zur Verlängerung",
     "fr": "un certificat à renouveler",
     "es": "un certificado en renovación",
     "doc": {"rows": [
         {"name": "renewal_date", "means": "наступает срок продления",
          "status": "unverified", "ground": ""},
         {"name": "operator_certified", "means": "у оператора есть допуск",
          "status": "verified", "ground": "sertifikat",
          "ground_kind": "certificate", "expires_on": "renewal_date"},
         {"name": "training_done", "means": "обучение пройдено",
          "status": "verified", "ground": "zhurnal"},
         {"name": "may_operate", "means": "оператору можно к работе",
          "status": "defined",
          "ground": "Tr(operator_certified) & Tr(training_done)"}],
         "claim": "may_operate"}},
]


# ГЛОССЫ ПО ЯЗЫКАМ. Найдено куратором 2026-09-04: он выбрал Агриппу на
# английском и получил в таблице РУССКИЕ пояснения. Промерено — не случай, а
# класс: 58 строк в 26 примерах из 41 несли русский `means`, а документ у
# примера ОДИН на все семь языков. Название и вопрос локализованы давно
# (`label`, `ask_<язык>`), документ — нет; незаметно это было ровно потому,
# что разработка шла по-русски и свой язык не бросается в глаза.
#
# Ключ — САМА РУССКАЯ ФРАЗА, а не выдуманный код: перевод стоит рядом с тем,
# что переводится, и новая строка примера не может сослаться на ключ, которого
# нет. Нет перевода — остаётся русский, то есть прежнее поведение: молчаливой
# потери текста не бывает, бывает непереведённый текст, и он виден.
ГЛОССЫ = {
 "это предложение ложно": {
  "en": "this sentence is false",
  "de": "dieser Satz ist falsch",
  "uk": "це речення хибне",
  "he": "משפט זה שקרי",
  "fr": "cette phrase est fausse",
  "es": "esta oración es falsa"
 },
 "брадобрей бреет самого себя": {
  "en": "the barber shaves himself",
  "de": "der Barbier rasiert sich selbst",
  "uk": "голяр голить сам себе",
  "he": "הספר מגלח את עצמו",
  "fr": "le barbier se rase lui-même",
  "es": "el barbero se afeita a sí mismo"
 },
 "«гетерологичное» не описывает само себя": {
  "en": "'heterological' does not describe itself",
  "de": "„heterologisch“ beschreibt sich selbst nicht",
  "uk": "«гетерологічне» не описує саме себе",
  "he": "«הטרולוגי» אינו מתאר את עצמו",
  "fr": "« hétérologique » ne se décrit pas lui-même",
  "es": "«heterológico» no se describe a sí mismo"
 },
 "a принадлежит a": {
  "en": "a belongs to a",
  "de": "a gehört zu a",
  "uk": "a належить a",
  "he": "a שייך ל-a",
  "fr": "a appartient à a",
  "es": "a pertenece a a"
 },
 "a принадлежит b": {
  "en": "a belongs to b",
  "de": "a gehört zu b",
  "uk": "a належить b",
  "he": "a שייך ל-b",
  "fr": "a appartient à b",
  "es": "a pertenece a b"
 },
 "a принадлежит R": {
  "en": "a belongs to R",
  "de": "a gehört zu R",
  "uk": "a належить R",
  "he": "a שייך ל-R",
  "fr": "a appartient à R",
  "es": "a pertenece a R"
 },
 "b принадлежит a": {
  "en": "b belongs to a",
  "de": "b gehört zu a",
  "uk": "b належить a",
  "he": "b שייך ל-a",
  "fr": "b appartient à a",
  "es": "b pertenece a a"
 },
 "b принадлежит b": {
  "en": "b belongs to b",
  "de": "b gehört zu b",
  "uk": "b належить b",
  "he": "b שייך ל-b",
  "fr": "b appartient à b",
  "es": "b pertenece a b"
 },
 "b принадлежит R": {
  "en": "b belongs to R",
  "de": "b gehört zu R",
  "uk": "b належить R",
  "he": "b שייך ל-R",
  "fr": "b appartient à R",
  "es": "b pertenece a R"
 },
 "R принадлежит a": {
  "en": "R belongs to a",
  "de": "R gehört zu a",
  "uk": "R належить a",
  "he": "R שייך ל-a",
  "fr": "R appartient à a",
  "es": "R pertenece a a"
 },
 "R принадлежит b": {
  "en": "R belongs to b",
  "de": "R gehört zu b",
  "uk": "R належить b",
  "he": "R שייך ל-b",
  "fr": "R appartient à b",
  "es": "R pertenece a b"
 },
 "R принадлежит самому себе": {
  "en": "R belongs to itself",
  "de": "R gehört zu sich selbst",
  "uk": "R належить сам собі",
  "he": "R שייך לעצמו",
  "fr": "R s'appartient à lui-même",
  "es": "R se pertenece a sí mismo"
 },
 "написанное на обороте — правда": {
  "en": "what is written on the back is true",
  "de": "was auf der Rückseite steht, ist wahr",
  "uk": "написане на звороті — правда",
  "he": "מה שכתוב מאחור הוא אמת",
  "fr": "ce qui est écrit au dos est vrai",
  "es": "lo escrito al dorso es verdadero"
 },
 "написанное на лицевой стороне — ложь": {
  "en": "what is written on the front is false",
  "de": "was auf der Vorderseite steht, ist falsch",
  "uk": "написане на лицьовому боці — брехня",
  "he": "מה שכתוב מלפנים הוא שקר",
  "fr": "ce qui est écrit au recto est faux",
  "es": "lo escrito en el anverso es falso"
 },
 "крокодил возвращает ребёнка": {
  "en": "the crocodile returns the child",
  "de": "das Krokodil gibt das Kind zurück",
  "uk": "крокодил повертає дитину",
  "he": "התנין מחזיר את הילד",
  "fr": "le crocodile rend l'enfant",
  "es": "el cocodrilo devuelve al niño"
 },
 "мать угадала, что он сделает": {
  "en": "the mother guessed what he would do",
  "de": "die Mutter hat erraten, was er tun wird",
  "uk": "мати вгадала, що він зробить",
  "he": "האם ניחשה מה הוא יעשה",
  "fr": "la mère a deviné ce qu'il ferait",
  "es": "la madre adivinó lo que él haría"
 },
 "первое предложение цикла истинно": {
  "en": "the first sentence of the cycle is true",
  "de": "der erste Satz des Zyklus ist wahr",
  "uk": "перше речення циклу істинне",
  "he": "המשפט הראשון במחזור אמיתי",
  "fr": "la première phrase du cycle est vraie",
  "es": "la primera oración del ciclo es verdadera"
 },
 "второе предложение цикла истинно": {
  "en": "the second sentence of the cycle is true",
  "de": "der zweite Satz des Zyklus ist wahr",
  "uk": "друге речення циклу істинне",
  "he": "המשפט השני במחזור אמיתי",
  "fr": "la deuxième phrase du cycle est vraie",
  "es": "la segunda oración del ciclo es verdadera"
 },
 "третье предложение цикла истинно": {
  "en": "the third sentence of the cycle is true",
  "de": "der dritte Satz des Zyklus ist wahr",
  "uk": "третє речення циклу істинне",
  "he": "המשפט השלישי במחזור אמיתי",
  "fr": "la troisième phrase du cycle est vraie",
  "es": "la tercera oración del ciclo es verdadera"
 },
 "четвёртое предложение цикла истинно": {
  "en": "the fourth sentence of the cycle is true",
  "de": "der vierte Satz des Zyklus ist wahr",
  "uk": "четверте речення циклу істинне",
  "he": "המשפט הרביעי במחזור אמיתי",
  "fr": "la quatrième phrase du cycle est vraie",
  "es": "la cuarta oración del ciclo es verdadera"
 },
 "предложение Карри истинно": {
  "en": "the Curry sentence is true",
  "de": "der Curry-Satz ist wahr",
  "uk": "речення Каррі істинне",
  "he": "משפט קארי אמיתי",
  "fr": "la phrase de Curry est vraie",
  "es": "la oración de Curry es verdadera"
 },
 "невозможное имеет место": {
  "en": "the impossible holds",
  "de": "das Unmögliche gilt",
  "uk": "неможливе має місце",
  "he": "הבלתי אפשרי מתקיים",
  "fr": "l'impossible vaut",
  "es": "lo imposible se da"
 },
 "следствие Карри истинно": {
  "en": "the consequent of Curry is true",
  "de": "der Nachsatz von Curry ist wahr",
  "uk": "наслідок Каррі істинний",
  "he": "העוקב של קארי אמיתי",
  "fr": "le conséquent de Curry est vrai",
  "es": "el consecuente de Curry es verdadero"
 },
 "это предложение не истинно": {
  "en": "this sentence is not true",
  "de": "dieser Satz ist nicht wahr",
  "uk": "це речення не істинне",
  "he": "משפט זה אינו אמיתי",
  "fr": "cette phrase n'est pas vraie",
  "es": "esta oración no es verdadera"
 },
 "это предложение не является заработанной истиной": {
  "en": "this sentence is not an earned truth",
  "de": "dieser Satz ist keine verdiente Wahrheit",
  "uk": "це речення не є заробленою істиною",
  "he": "משפט זה אינו אמת שהורווחה",
  "fr": "cette phrase n'est pas une vérité méritée",
  "es": "esta oración no es una verdad ganada"
 },
 "это предложение доказуемо": {
  "en": "this sentence is provable",
  "de": "dieser Satz ist beweisbar",
  "uk": "це речення доказовне",
  "he": "משפט זה ניתן להוכחה",
  "fr": "cette phrase est démontrable",
  "es": "esta oración es demostrable"
 },
 "это предложение истинно": {
  "en": "this sentence is true",
  "de": "dieser Satz ist wahr",
  "uk": "це речення істинне",
  "he": "משפט זה אמיתי",
  "fr": "cette phrase est vraie",
  "es": "esta oración es verdadera"
 },
 "множество S принадлежит самому себе": {
  "en": "the set S belongs to itself",
  "de": "die Menge S gehört zu sich selbst",
  "uk": "множина S належить сама собі",
  "he": "הקבוצה S שייכת לעצמה",
  "fr": "l'ensemble S s'appartient à lui-même",
  "es": "el conjunto S se pertenece a sí mismo"
 },
 "A истинно": {
  "en": "A is true",
  "de": "A ist wahr",
  "uk": "A істинне",
  "he": "A אמיתי",
  "fr": "A est vrai",
  "es": "A es verdadero"
 },
 "B истинно": {
  "en": "B is true",
  "de": "B ist wahr",
  "uk": "B істинне",
  "he": "B אמיתי",
  "fr": "B est vrai",
  "es": "B es verdadero"
 },
 "ни одно из последующих не истинно": {
  "en": "none of the later ones is true",
  "de": "keiner der späteren ist wahr",
  "uk": "жодне з подальших не істинне",
  "he": "אף אחד מהבאים אינו אמיתי",
  "fr": "aucune des suivantes n'est vraie",
  "es": "ninguna de las siguientes es verdadera"
 },
 "сказанное Смитом истинно": {
  "en": "what Smith said is true",
  "de": "was Smith gesagt hat, ist wahr",
  "uk": "сказане Смітом істинне",
  "he": "מה שסמית אמר אמיתי",
  "fr": "ce que Smith a dit est vrai",
  "es": "lo que dijo Smith es verdadero"
 },
 "сказанное Джонсом истинно": {
  "en": "what Jones said is true",
  "de": "was Jones gesagt hat, ist wahr",
  "uk": "сказане Джонсом істинне",
  "he": "מה שג'ונס אמר אמיתי",
  "fr": "ce que Jones a dit est vrai",
  "es": "lo que dijo Jones es verdadero"
 },
 "титул принадлежит кораблю A": {
  "en": "the title belongs to ship A",
  "de": "der Titel gehört Schiff A",
  "uk": "титул належить кораблю A",
  "he": "התואר שייך לספינה A",
  "fr": "le titre appartient au navire A",
  "es": "el título pertenece al barco A"
 },
 "титул принадлежит кораблю B": {
  "en": "the title belongs to ship B",
  "de": "der Titel gehört Schiff B",
  "uk": "титул належить кораблю B",
  "he": "התואר שייך לספינה B",
  "fr": "le titre appartient au navire B",
  "es": "el título pertenece al barco B"
 },
 "утверждение, стоящее на фундаменте": {
  "en": "a claim standing on the foundation",
  "de": "eine Behauptung, die auf dem Fundament steht",
  "uk": "твердження, що стоїть на фундаменті",
  "he": "טענה העומדת על היסוד",
  "fr": "une affirmation reposant sur le fondement",
  "es": "una afirmación que se apoya en el fundamento"
 },
 "фундамент держится сам собой": {
  "en": "the foundation holds itself up",
  "de": "das Fundament trägt sich selbst",
  "uk": "фундамент тримається сам собою",
  "he": "היסוד נתמך בעצמו",
  "fr": "le fondement se soutient lui-même",
  "es": "el fundamento se sostiene a sí mismo"
 },
 "реестр залогов перечитывают": {
  "en": "the lien registry is re-read",
  "de": "das Pfandregister wird erneut gelesen",
  "uk": "реєстр застав перечитують",
  "he": "מרשם השעבודים נקרא מחדש",
  "fr": "le registre des gages est relu",
  "es": "el registro de gravámenes se vuelve a leer"
 },
 "машина не в залоге": {
  "en": "the car is not pledged",
  "de": "das Auto ist nicht verpfändet",
  "uk": "автомобіль не в заставі",
  "he": "הרכב אינו משועבד",
  "fr": "la voiture n'est pas gagée",
  "es": "el coche no está pignorado"
 },
 "документы в порядке": {
  "en": "the papers are in order",
  "de": "die Papiere sind in Ordnung",
  "uk": "документи в порядку",
  "he": "המסמכים תקינים",
  "fr": "les papiers sont en règle",
  "es": "los papeles están en regla"
 },
 "сделку можно закрывать": {
  "en": "the deal may be closed",
  "de": "das Geschäft darf abgeschlossen werden",
  "uk": "угоду можна закривати",
  "he": "אפשר לסגור את העסקה",
  "fr": "l'affaire peut être conclue",
  "es": "el trato puede cerrarse"
 },
 "наступает срок продления": {
  "en": "the renewal date falls due",
  "de": "der Verlängerungstermin wird fällig",
  "uk": "настає термін продовження",
  "he": "מועד החידוש מגיע",
  "fr": "la date de renouvellement échoit",
  "es": "vence el plazo de renovación"
 },
 "у оператора есть допуск": {
  "en": "the operator holds a clearance",
  "de": "der Bediener hat eine Zulassung",
  "uk": "оператор має допуск",
  "he": "למפעיל יש היתר",
  "fr": "l'opérateur détient une habilitation",
  "es": "el operador tiene autorización"
 },
 "обучение пройдено": {
  "en": "the training is completed",
  "de": "die Schulung ist absolviert",
  "uk": "навчання пройдено",
  "he": "ההכשרה הושלמה",
  "fr": "la formation est suivie",
  "es": "la formación está completada"
 },
 "оператору можно к работе": {
  "en": "the operator may start work",
  "de": "der Bediener darf an die Arbeit",
  "uk": "оператора можна допускати до роботи",
  "he": "המפעיל רשאי להתחיל לעבוד",
  "fr": "l'opérateur peut se mettre au travail",
  "es": "el operador puede ponerse a trabajar"
 }
}


def _локализовать(doc, lang):
    """Тот же документ, но с пояснениями на языке читателя.

    Копия, а не правка на месте: EXAMPLES — модульная константа, и подмена в
    ней означала бы, что первый же запрос на немецком навсегда испортит
    примеры для всех остальных.
    """
    if lang == "ru":
        return doc
    строки = []
    for r in doc.get("rows") or []:
        пер = ГЛОССЫ.get(r.get("means", ""), {}).get(lang)
        строки.append(dict(r, means=пер) if пер else dict(r))
    return dict(doc, rows=строки)


def catalogue(lang="en"):
    """Kinds and their cases, for the two drop-downs."""
    kinds = [{"key": k, "label": v.get(lang, v["en"])}
             for k, v in KINDS.items()]
    items = [{"kind": e["kind"], "label": e.get(lang, e["en"]),
              # the question the example ANSWERS, so the chat shows what is
              # being asked rather than a verdict with no question above it
              "ask": e.get(f"ask_{lang}") or e.get("ask_en", ""),
              "doc": _локализовать(e["doc"], lang)} for e in EXAMPLES]
    return {"kinds": kinds, "items": items}
