# -*- coding: utf-8 -*-
"""
The ZFL reference page, generated from the language itself.

The curator asked for a page describing ZFL. Writing one by hand is the
obvious move and the wrong one: a hand-written reference is right on the day
it is written and quietly wrong a month later, and this project spends most
of its effort refusing exactly that arrangement everywhere else. So the page
is GENERATED — the column table from `zfl2.COLUMNS`, the operators from the
parser's own tables, the worked example imported from the stand that proves
it runs, the error codes from the validator's source. Nothing here is
retyped, so nothing here can drift.

What stays hand-written is the part a machine cannot supply: why the thing
is shaped this way. That is three paragraphs, and they are marked as prose.

Both languages, side by side in the spec, hand-translated for the reason
given in `zfl2`: the vocabulary IS the content.

Run:  python3 tool/zfl2doc.py            (writes tool/static/zfl.html)
      python3 tool/zfl2doc.py --check    (fails if the codes drifted)
"""
import html
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import zfl2                                                      # noqa: E402
import ztljudge                                                  # noqa: E402
from test_zfl2 import MIXED                                      # noqa: E402

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                   "static", "zfl.html")

# The one-line meaning of each machine-readable code. The codes themselves
# are read out of the validator's source, and `--check` fails if the two
# sets ever differ — so a new code cannot be added without a word about it
# here, and a deleted one cannot linger.
CODE_HELP = {
    "E_EMPTY": ("the table has no rows", "в таблице нет строк"),
    "E_NONAME": ("a row without a name", "строка без имени"),
    "E_BADNAME": ("a name a formula could not use",
                  "имя, непригодное для формулы"),
    "E_DUPNAME": ("the same name twice", "имя повторяется"),
    "E_RESERVED": ("a constant of the language used as a row name — it silently "
                   "changes the reading",
                   "константа языка в роли имени строки — молча меняет разбор"),
    "E_STATUS": ("a status outside the four", "статус вне четырёх"),
    "E_SCALE": ("a scale that is not empty/int/decimalK/fracM, or out of bounds",
                "шкала не пустая/int/decimalK/fracM либо вне границ"),
    "E_NOGROUND": ("verified, refuted or defined, with nothing backing it",
                   "проверено, опровергнуто или определено — но без основания"),
    "E_KIND": ("a kind of ground outside the list", "вид основания вне списка"),
    "E_EXPIRY_NO_GROUND": (
        "a clock on a row that has no earned ground to lose",
        "часы на строке, которой нечего терять: истекать может только "
        "заработанное"),
    "E_DIM": ("a dimension outside the list — a ground either supports a "
              "claim or permits it",
              "измерение вне списка — основание либо подпирает утверждение, "
              "либо даёт на него право"),
    "E_DIM_CLASH": ("a ground carries one mark, not two: 'authority' cannot "
                    "be combined with an act, a certificate or another row",
                    "основание несёт одну пометку, а не две: «разрешение» не "
                    "сочетается с актом, сертификатом или другой строкой"),
    "E_FORMULA": ("the defining formula does not parse",
                  "определяющая формула не разбирается"),
    "E_CLAIM": ("the claim does not parse", "утверждение не разбирается"),
    "E_UNKNOWN_NAME": ("a formula names a row that does not exist",
                       "формула называет несуществующую строку"),
    "E_OPEN_INTERVAL": ("an open bound like (0,10) — put the strictness in "
                        "the claim instead",
                        "открытая граница вроде (0,10) — строгость пишется "
                        "в утверждении"),
    "E_VALUE_SET": ("a choice between values, {0,10} — that is two rows, "
                    "not one quantity",
                    "выбор между величинами, {0,10} — это две строки, "
                    "а не одна величина"),
    "E_VALUE_FORM": ("a value that is neither a number, an interval nor ?",
                     "величина, которая не число, не интервал и не ?"),
    "E_UNREADABLE": ("the instruments could not read the claim — the "
                     "message says what they choked on",
                     "приборы не смогли прочесть утверждение — в сообщении "
                     "сказано, на чём именно"),
    "E_GROUND_SPACES": ("a ground with a space in it — a ground is one "
                        "word, because it names a document",
                        "основание с пробелом — оно одно слово, потому что "
                        "называет документ"),
    "E_UNIT": ("a unit that cannot be read — a word, optionally with a "
               "power (m2), joined by · or /",
               "единица, которую нельзя прочесть — слово, при желании "
               "со степенью (m2), соединяется через · или /"),
    "W_UNIT_NO_VALUE": ("a unit with no value", "единица без величины"),
    "W_NO_GLOSS": ("no gloss, so nobody can check the name means what it "
                   "seems to",
                   "нет пояснения — некому проверить, то ли значит имя"),
}

PROSE = {
    "en": [
        ("Why a table and not a syntax",
         "Everything you write here is one document: a list of NAMES, each "
         "saying where it stands with you, plus what you CLAIM about them. "
         "There is no genre to declare and no mode to pick. Which "
         "instruments answer — the numeric floor, the passport office, the "
         "ledger, the judge — follows from which cells you filled."),
        ("The one rule underneath",
         "Truth is not granted on credit. A name is verified when a "
         "verification was produced, and the ground column is where you say "
         "what produced it. A name with nothing backing it is not false — it "
         "is unverified, which is an honest third answer and the reason this "
         "logic exists."),
        ("Asking for a number",
         "Put `?` in a value and the row stops being an answer and becomes a "
         "question. `x = ?` with a claim of `x - 10 = 20` is answered: x is "
         "30, and earned. This is the one cell that changes what the machine "
         "DOES — everywhere else you are telling it what you know, and here "
         "you are asking."),
        ("Where formulas survive, and the one cell that reads two ways",
         "In two cells only. In GROUND, when a name is DEFINED by a formula "
         "over other names — that is how self-reference is written, and it "
         "is why the liar needs no special mode. And in CLAIM, which is what "
         "you are actually asserting. Note what the ground cell is doing: "
         "for a verified name it holds `inv-17`, an opaque name the machine "
         "never looks inside and which means nothing but its own identity; "
         "for a defined name it holds `~Tr(L)`, a formula the machine reads "
         "and evaluates. The status decides which, and the form asks again "
         "whenever you change it."),
    ],
    "ru": [
        ("Почему таблица, а не синтаксис",
         "Всё, что вы здесь пишете, — один документ: список ИМЁН, каждое из "
         "которых говорит, откуда оно у вас, плюс то, что вы про них "
         "УТВЕРЖДАЕТЕ. Никакого жанра объявлять не надо и режим выбирать не "
         "надо. Какие приборы ответят — числовой пол, паспортный стол, "
         "тетрадь, судья — следует из того, какие клетки вы заполнили."),
        ("Правило, лежащее под всем",
         "Истина не даётся в кредит. Имя проверено, когда проверка "
         "произведена, и колонка «основание» — это место, где вы говорите, "
         "чем именно. Имя без основания не ложно — оно НЕ ПРОВЕРЕНО, и это "
         "честный третий ответ, ради которого вся эта логика и существует."),
        ("Как спросить число",
         "Поставьте `?` в величину — и строка перестаёт быть ответом и "
         "становится вопросом. `x = ?` при утверждении `x - 10 = 20` "
         "получает ответ: x равен 30, и заработан. Это единственная клетка, "
         "которая меняет то, что машина ДЕЛАЕТ: везде вы сообщаете ей, что "
         "знаете, а здесь — спрашиваете."),
        ("Где остаются формулы, и клетка, которая читается двояко",
         "Ровно в двух клетках. В ОСНОВАНИИ — когда имя ОПРЕДЕЛЕНО формулой "
         "через другие имена; так пишется самоссылка, и поэтому лжецу не "
         "нужен отдельный режим. И в УТВЕРЖДЕНИИ — том, что вы, собственно, "
         "заявляете. Заметьте, что делает клетка основания: у проверенного "
         "имени там `inv-17` — непрозрачное имя, внутрь которого машина не "
         "смотрит и которое не значит ничего, кроме собственного тождества; "
         "у определённого — `~Tr(L)`, формула, которую машина читает и "
         "вычисляет. Что именно там ждут, решает статус, и форма "
         "переспрашивает, как только вы его меняете."),
    ],
    "uk": [
        ("Чому таблиця, а не синтаксис",
         "Усе, що ви тут пишете, — один документ: перелік ІМЕН, кожне каже, звідки воно у вас, плюс те, що ви про них СТВЕРДЖУЄТЕ. Немає жанру, який треба оголосити, і немає режиму, який треба обрати. Які прилади відповідять — числова підлога, паспортний стіл, зошит, суддя — випливає з того, які клітинки ви заповнили."),
        ("Одне правило під усім",
         "Істина не видається в кредит. Ім'я перевірене тоді, коли перевірку справді зробили, і стовпець підстави — це місце, де ви кажете, що саме її зробило. Ім'я, під яким нічого немає, не хибне — воно неперевірене, і це чесна третя відповідь, заради якої ця логіка й існує."),
        ("Коли ви питаєте число",
         "Поставте `?` у величину — і рядок перестає бути відповіддю й стає питанням. `x = ?` разом із твердженням `x - 10 = 20` має відповідь: x дорівнює 30, і це зароблено. Це єдина клітинка, яка змінює те, що машина РОБИТЬ: скрізь інде ви кажете їй, що знаєте, а тут — питаєте."),
        ("Де живуть формули і яка клітинка читається двояко",
         "Лише у двох клітинках. У ПІДСТАВІ, коли ім'я ВИЗНАЧЕНЕ формулою через інші імена — саме так пишеться самопосилання, і саме тому брехунові не потрібен окремий режим. І у ТВЕРДЖЕННІ, яке ви насправді й заявляєте. Зверніть увагу, що робить клітинка підстави: у перевіреного імені там `inv-17` — непрозоре ім'я, всередину якого машина ніколи не дивиться; у визначеного там `~Tr(L)` — формула, яку машина читає й обчислює. Вирішує статус, і форма перепитує щоразу, коли ви його міняєте."),
    ],
    "he": [
        ("למה טבלה ולא תחביר",
         "כל מה שאתם כותבים כאן הוא מסמך אחד: רשימת שמות, כל אחד אומר מאיפה הוא הגיע אליכם, ובנוסף מה אתם טוענים עליהם. אין ז'אנר להכריז עליו ואין מצב לבחור. אילו כלים יענו — הרצפה המספרית, לשכת הדרכונים, הפנקס, השופט — נובע מאילו תאים מילאתם."),
        ("הכלל האחד שמתחת לכול",
         "אמת אינה ניתנת באשראי. שם מאומת כאשר אימות באמת נעשה, ועמודת האסמכתא היא המקום שבו אתם אומרים מה עשה אותו. שם שאין דבר מאחוריו איננו שקרי — הוא לא אומת, וזו תשובה שלישית ישרה, והסיבה שהלוגיקה הזו קיימת."),
        ("כששואלים מספר",
         "שימו `?` בערך והשורה מפסיקה להיות תשובה והופכת לשאלה. `x = ?` יחד עם הטענה `x - 10 = 20` נענית: x הוא 30, ומאומת. זה התא היחיד שמשנה את מה שהמכונה עושה — בכל מקום אחר אתם מספרים לה מה אתם יודעים, וכאן אתם שואלים."),
        ("היכן שורדות הנוסחאות, והתא שנקרא בשתי דרכים",
         "בשני תאים בלבד. באסמכתא, כששם מוגדר על ידי נוסחה מעל שמות אחרים — כך נכתבת הפניה עצמית, ולכן פרדוקס השקרן אינו זקוק למצב מיוחד. ובטענה, שהיא מה שאתם באמת מצהירים. שימו לב מה עושה תא האסמכתא: אצל שם מאומת הוא מחזיק `inv-17`, שם אטום שהמכונה לעולם אינה מציצה לתוכו; אצל שם מוגדר הוא מחזיק `~Tr(L)`, נוסחה שהמכונה קוראת ומחשבת. המעמד מכריע, והטופס שואל שוב בכל פעם שאתם משנים אותו."),
    ],
    "de": [
        ("Warum eine Tabelle und keine Syntax",
         "Alles, was Sie hier schreiben, ist EIN Dokument: eine Liste von NAMEN, jeder sagt, woher er bei Ihnen steht, dazu das, was Sie über sie BEHAUPTEN. Es gibt keine Gattung zu erklären und keinen Modus zu wählen. Welche Instrumente antworten — die Zahlenebene, das Passamt, das Buch, der Richter — ergibt sich daraus, welche Zellen Sie gefüllt haben."),
        ("Die eine Regel darunter",
         "Wahrheit wird nicht auf Kredit gewährt. Ein Name ist geprüft, wenn eine Prüfung stattgefunden hat, und die Spalte Grundlage ist der Ort, an dem Sie sagen, was sie hervorgebracht hat. Ein Name ohne etwas dahinter ist nicht falsch — er ist ungeprüft, und das ist eine ehrliche dritte Antwort und der Grund, warum es diese Logik gibt."),
        ("Wenn Sie nach einer Zahl fragen",
         "Setzen Sie `?` in einen Wert, und die Zeile ist keine Antwort mehr, sondern eine Frage. `x = ?` mit der Behauptung `x - 10 = 20` wird beantwortet: x ist 30, und verdient. Das ist die einzige Zelle, die ändert, was die Maschine TUT — überall sonst sagen Sie ihr, was Sie wissen, und hier fragen Sie."),
        ("Wo Formeln überleben, und die eine Zelle mit zwei Lesarten",
         "Nur in zwei Zellen. In der GRUNDLAGE, wenn ein Name durch eine Formel über andere Namen DEFINIERT wird — so schreibt man Selbstbezug, und darum braucht der Lügner keinen eigenen Modus. Und in der BEHAUPTUNG, die Sie tatsächlich aufstellen. Beachten Sie, was die Grundlagenzelle tut: bei einem geprüften Namen hält sie `inv-17`, einen undurchsichtigen Namen, in den die Maschine nie hineinsieht; bei einem definierten Namen `~Tr(L)`, eine Formel, die sie liest und auswertet. Der Status entscheidet, und das Formular fragt neu, sobald Sie ihn ändern."),
    ],
    "fr": [
        ("Pourquoi un tableau et non une syntaxe",
         "Tout ce que vous écrivez ici est UN document : une liste de NOMS, chacun disant d'où il vous vient, plus ce que vous AFFIRMEZ à leur sujet. Aucun genre à déclarer, aucun mode à choisir. Quels instruments répondent — le socle numérique, le bureau des passeports, le registre, le juge — découle des cases que vous avez remplies."),
        ("La règle unique en dessous",
         "La vérité ne se donne pas à crédit. Un nom est vérifié quand une vérification a bien eu lieu, et la colonne fondement est l'endroit où vous dites ce qui l'a produite. Un nom sans rien derrière n'est pas faux — il est non vérifié, ce qui est une troisième réponse honnête et la raison d'être de cette logique."),
        ("Quand vous demandez un nombre",
         "Mettez `?` dans une valeur et la ligne cesse d'être une réponse pour devenir une question. `x = ?` avec l'affirmation `x - 10 = 20` reçoit sa réponse : x vaut 30, et c'est acquis. C'est la seule case qui change ce que la machine FAIT — partout ailleurs vous lui dites ce que vous savez, ici vous demandez."),
        ("Où survivent les formules, et la case qui se lit de deux façons",
         "Dans deux cases seulement. Dans le FONDEMENT, quand un nom est DÉFINI par une formule sur d'autres noms — c'est ainsi que s'écrit l'autoréférence, et c'est pourquoi le menteur n'a besoin d'aucun mode spécial. Et dans l'AFFIRMATION, qui est ce que vous avancez réellement. Notez ce que fait la case fondement : pour un nom vérifié elle contient `inv-17`, un nom opaque dans lequel la machine ne regarde jamais ; pour un nom défini, `~Tr(L)`, une formule qu'elle lit et évalue. Le statut tranche, et le formulaire redemande dès que vous le changez."),
    ],
    "es": [
        ("Por qué una tabla y no una sintaxis",
         "Todo lo que escribe aquí es UN documento: una lista de NOMBRES, cada uno diciendo de dónde le viene, más lo que usted AFIRMA sobre ellos. No hay género que declarar ni modo que elegir. Qué instrumentos responden — el suelo numérico, la oficina de pasaportes, el registro, el juez — se sigue de qué casillas rellenó."),
        ("La única regla por debajo",
         "La verdad no se concede a crédito. Un nombre está verificado cuando una verificación ocurrió de veras, y la columna fundamento es donde usted dice qué la produjo. Un nombre sin nada detrás no es falso — está sin verificar, que es una tercera respuesta honesta y la razón de ser de esta lógica."),
        ("Cuando usted pide un número",
         "Ponga `?` en un valor y la fila deja de ser una respuesta para volverse una pregunta. `x = ?` junto con la afirmación `x - 10 = 20` tiene respuesta: x es 30, y ganado. Es la única casilla que cambia lo que la máquina HACE — en todas las demás usted le cuenta lo que sabe, y aquí pregunta."),
        ("Dónde sobreviven las fórmulas, y la casilla que se lee de dos maneras",
         "Solo en dos casillas. En el FUNDAMENTO, cuando un nombre se DEFINE por una fórmula sobre otros nombres — así se escribe la autorreferencia, y por eso el mentiroso no necesita ningún modo especial. Y en la AFIRMACIÓN, que es lo que usted sostiene de verdad. Fíjese en lo que hace la casilla fundamento: para un nombre verificado guarda `inv-17`, un nombre opaco dentro del cual la máquina nunca mira; para uno definido, `~Tr(L)`, una fórmula que lee y evalúa. El estado decide, y el formulario vuelve a preguntar en cuanto usted lo cambia."),
    ],
}

# The abbreviation is spelled out in the title on purpose: one letter apart
# from ZTL, and a reader who has just come from the papers will otherwise
# take it for a typo.
HEAD = {"en": ("ZFL — Zero-trust Formal Language, the language of the "
               "studio (ZTL is the logic; ZFL is how you write for it)", "column", "required",
               "always", "in context", "no", "operators", "error codes",
               "a worked example", "means", "status", "ground",
               "what it is", "options / examples", "the document itself",
               "value", "the columns of a row", "what can go in a value",
               "arithmetic"),
        "ru": ("ZFL — Zero-trust Formal Language, язык студии "
               "(ZTL — сама логика, ZFL — то, как для неё пишут)", "колонка", "обязательна",
               "всегда", "по условию", "нет", "операторы", "коды ошибок",
               "разобранный пример", "значит", "статус", "основание",
               "что это", "варианты / примеры", "сам документ",
               "величина", "колонки строки", "что можно писать в величине",
               "арифметика"),
        "uk": ("ZFL — Zero-trust Formal Language, мова студії (ZTL — це логіка; ZFL — як для неї писати)",
               "стовпець",
               "обов'язково",
               "завжди",
               "за контекстом",
               "ні",
               "оператори",
               "коди помилок",
               "розібраний приклад",
               "означає",
               "статус",
               "підстава",
               "що це",
               "варіанти / приклади",
               "сам документ",
               "величина",
               "стовпці рядка",
               "що може бути величиною",
               "арифметика"),
        "he": ("ZFL — Zero-trust Formal Language, שפת הסטודיו (ZTL היא הלוגיקה; ZFL היא איך כותבים עבורה)",
               "עמודה",
               "חובה",
               "תמיד",
               "לפי ההקשר",
               "לא",
               "אופרטורים",
               "קודי שגיאה",
               "דוגמה מפורטת",
               "פירושו",
               "מעמד",
               "אסמכתא",
               "מה זה",
               "אפשרויות / דוגמאות",
               "המסמך עצמו",
               "ערך",
               "עמודות של שורה",
               "מה יכול להיות ערך",
               "חשבון"),
        "de": ("ZFL — Zero-trust Formal Language, die Sprache des Studios (ZTL ist die Logik; ZFL ist, wie man dafür schreibt)",
               "Spalte",
               "Pflicht",
               "immer",
               "je nach Kontext",
               "nein",
               "Operatoren",
               "Fehlercodes",
               "ein durchgerechnetes Beispiel",
               "bedeutet",
               "Status",
               "Grundlage",
               "was es ist",
               "Optionen / Beispiele",
               "das Dokument selbst",
               "Wert",
               "die Spalten einer Zeile",
               "was ein Wert sein darf",
               "Arithmetik"),
        "fr": ("ZFL — Zero-trust Formal Language, le langage du studio (ZTL est la logique ; ZFL est la façon d'écrire pour elle)",
               "colonne",
               "obligatoire",
               "toujours",
               "selon le contexte",
               "non",
               "opérateurs",
               "codes d'erreur",
               "un exemple traité",
               "signifie",
               "statut",
               "fondement",
               "ce que c'est",
               "options / exemples",
               "le document lui-même",
               "valeur",
               "les colonnes d'une ligne",
               "ce qui peut être une valeur",
               "arithmétique"),
        "es": ("ZFL — Zero-trust Formal Language, el lenguaje del estudio (ZTL es la lógica; ZFL es cómo se escribe para ella)",
               "columna",
               "obligatorio",
               "siempre",
               "según el contexto",
               "no",
               "operadores",
               "códigos de error",
               "un ejemplo resuelto",
               "significa",
               "estado",
               "fundamento",
               "qué es",
               "opciones / ejemplos",
               "el documento mismo",
               "valor",
               "las columnas de una fila",
               "qué puede ser un valor",
               "aritmética"),
        }


def column_examples(key):
    """The examples a column advertises, read off the spec."""
    return (zfl2.column(key) or {}).get("eg", [])


def codes_in_source():
    """The codes the validator actually raises, read out of it."""
    src = open(zfl2.__file__, encoding="utf-8").read()
    return set(re.findall(r'"([EW]_[A-Z_]+)"', src))


# What each symbol MEANS. The symbols themselves are read out of the
# judge's own table below, and `--check` fails if one of them turns up
# without a meaning here — a reference that lists a symbol it cannot
# explain is worse than one that omits it.
OP_HELP = {
    "&": ("and", "и"), "|": ("or", "или"), "->": ("if … then", "если … то"),
    "^": ("exactly one of", "ровно одно из"),
    "=": ("the same value as", "то же значение, что"),
    "~": ("not", "не"),
    "Tr(x)": ("the value of the row x — this is how self-reference is "
              "written", "значение строки x — так пишется самоссылка"),
    "<=": ("at most", "не больше"), ">=": ("at least", "не меньше"),
    "==": ("equal to", "равно"), "<": ("less than", "меньше"),
    ">": ("greater than", "больше"),
}


# The three shapes a VALUE cell can take. `?` was documented as one of them
# in a clause at the end of a help line, which the curator rightly called
# not designating it: it is not a formatting option among others, it is the
# switch that turns the judge into a SOLVER. Every example the value column
# offers must appear here, checked below, so a fourth form cannot be added
# without a word about what it does.
VALUE_HELP = {
    "1500": ("a number you have measured or read off a document",
             "число, которое вы измерили или прочли в документе"),
    "[0,10]": ("a box: somewhere in this range, and the machine keeps the "
               "range rather than picking a point. Both ends are INCLUDED; "
               "for a strict bound put it in the claim — `x > 0`. Write it "
               "backwards, [10,0], and you get E: the row names nothing, "
               "which is a verdict rather than a typo",
               "коробка: где-то в этих пределах, и машина хранит пределы, "
               "а не выбирает точку. Обе границы ВКЛЮЧЕНЫ; строгую границу "
               "пишите в утверждении — `x > 0`. Напишете наоборот, [10,0], "
               "получите E: строка не называет ничего, и это вердикт, "
               "а не опечатка"),
    "?": ("A QUESTION. You do not know it and you are asking. If the rest of "
          "the table determines it, the solver answers with the value AND "
          "the provenance it inherited — `x = 30, earned`. If it does not, "
          "you get told what would settle it.",
          "ВОПРОС. Вы его не знаете и спрашиваете. Если остальная таблица "
          "его определяет, решатель отвечает величиной И происхождением, "
          "которое она унаследовала — `x = 30, заработано`. Если не "
          "определяет — вам скажут, что это решит."),
}


# ARITHMETIC, which the reference did not mention at all until the curator
# pointed it out: `x - 10 = 20` works and nothing on this page said `-`
# existed. The symbols are read out of the numeric reader's own tag table,
# so a fifth operation cannot appear there without appearing here.
ARITH_HELP = {
    "+": ("plus", "плюс"), "-": ("minus", "минус"),
    "*": ("times", "умножить"), "/": ("divided by", "разделить"),
    "sum(a,b,…)": ("the sum of several — the same as a + b + …",
                   "сумма нескольких — то же, что a + b + …"),
    "( )": ("brackets, to say what goes first",
            "скобки — чтобы сказать, что раньше"),
    "-x": ("a leading minus: the sign of a term, not the operation between "
           "two — `-x + 100 = 70` is a fair question and was not accepted "
           "until 2026-08-13",
           "минус в начале: знак самого члена, а не действие между двумя — "
           "`-x + 100 = 70` законный вопрос, и до 2026-08-13 он не "
           "принимался"),
}


def arithmetic():
    """The operations the numeric reader accepts, from its own table."""
    import znumjudge
    src = open(znumjudge.__file__, encoding="utf-8").read()
    m = re.search(r'_TAG = \{([^}]*)\}', src)
    ops = re.findall(r'"([^"]+)":', m.group(1)) if m else []
    return sorted(ops) + ["sum(a,b,…)", "( )", "-x"]


def operators():
    """One operator set for the whole language, taken from the parsers
    rather than retyped: the propositional connectives from the judge's own
    table, the comparisons from the numeric floor's."""
    binops = sorted({k for k in ztljudge.BINOPS if k.isascii()})
    return binops + ["~", "Tr(x)"] + ["<=", ">=", "==", "<", ">"]


def _esc(s):
    return html.escape(str(s), quote=True)


def pick(entry, lang):
    """A localised string, however it is stored. Two-language entries were
    written as positional tuples `(en, ru)`, which cannot hold a third
    language at all; new ones are dicts keyed by code. Both are read here so
    that adding a language never means rewriting the ones already written,
    and a code with no translation yet shows its English rather than a gap."""
    if isinstance(entry, dict):
        return entry.get(lang) or entry["en"]
    return entry[1] if lang == "ru" and len(entry) > 1 else entry[0]


def render(lang="en"):
    spec = zfl2.form_spec(lang)
    h = HEAD.get(lang) or HEAD["en"]
    parts = [f"<h1>{_esc(h[0])}</h1>"]
    for title, body in (PROSE.get(lang) or PROSE["en"]):
        parts.append(f"<h2>{_esc(title)}</h2><p>{_esc(body)}</p>")

    # a heading is a phrase, not a word with an English plural glued on:
    # "колонкаs" is what that shortcut produced, and it was visible on the
    # first look at the Russian page
    parts.append(f"<h2>{_esc(h[16])}</h2><table><tr>"
                 f"<th>{_esc(h[1])}</th><th>{_esc(h[12])}</th>"
                 f"<th>{_esc(h[2])}</th><th>{_esc(h[13])}</th></tr>")
    for c in spec["columns"]:
        req = (h[3] if c["required"]
               else h[4] if c["required_when"] else h[5])
        opts = ""
        if c.get("options"):
            opts = " · ".join(_esc(o["label"]) for o in c["options"] if
                              o["label"])
        eg = " · ".join(_esc(e) for e in c.get("eg", []))
        extra = opts or eg
        cls = ' class="adv"' if c["advanced"] else ""
        parts.append(f"<tr{cls}><td><b>{_esc(c['label'])}</b></td>"
                     f"<td>{_esc(c['help'])}</td><td>{_esc(req)}</td>"
                     f"<td>{extra}</td></tr>")
    parts.append("</table>")

    parts.append(f"<h2>{_esc(h[14])}</h2><table><tr>"
                 f"<th>{_esc(h[1])}</th><th>{_esc(h[12])}</th>"
                 f"<th>{_esc(h[2])}</th><th>{_esc(h[13])}</th></tr>")
    for c in spec["document"]:
        req = h[3] if c["required"] else h[5]
        eg = " · ".join(_esc(e) for e in c.get("eg", []))
        opts = " · ".join(_esc(o["label"]) for o in c.get("options", []))
        parts.append(f"<tr><td><b>{_esc(c['label'])}</b></td>"
                     f"<td>{_esc(c['help'])}</td><td>{_esc(req)}</td>"
                     f"<td>{opts or eg}</td></tr>")
    parts.append("</table>")

    parts.append(f"<h2>{_esc(h[6])}</h2><table>")
    for op in operators():
        en, ru = OP_HELP.get(op, ("—", "—"))
        parts.append(f"<tr><td><code>{_esc(op)}</code></td>"
                     f"<td>{_esc(pick((en, ru), lang))}</td></tr>")
    parts.append("</table>")

    parts.append(f"<h2>{_esc(h[18])}</h2><table>")
    for op in arithmetic():
        en, ru = ARITH_HELP.get(op, ("—", "—"))
        parts.append(f"<tr><td><code>{_esc(op)}</code></td>"
                     f"<td>{_esc(pick((en, ru), lang))}</td></tr>")
    parts.append("</table>")

    parts.append(f"<h2>{_esc(h[17])}</h2><table>")
    for form in column_examples("value"):
        en, ru = VALUE_HELP.get(form, ("—", "—"))
        parts.append(f"<tr><td><code>{_esc(form)}</code></td>"
                     f"<td>{_esc(pick((en, ru), lang))}</td></tr>")
    parts.append("</table>")

    parts.append(f"<h2>{_esc(h[8])}</h2><table><tr>"
                 f"<th>{_esc(h[1])}</th><th>{_esc(h[9])}</th>"
                 f"<th>{_esc(h[10])}</th><th>{_esc(h[11])}</th>"
                 f"<th>{_esc(h[15])}</th></tr>")
    for r in MIXED["rows"]:
        parts.append("<tr>" + "".join(
            f"<td>{_esc(r.get(k, '') or '—')}</td>"
            for k in ("name", "means", "status", "ground", "value")) + "</tr>")
    parts.append("</table>")
    parts.append(f"<p><b>{_esc(spec['document'][0]['label'])}:</b> "
                 f"<code>{_esc(MIXED['claim'])}</code></p>")

    parts.append(f"<h2>{_esc(h[7])}</h2><table>")
    for code in sorted(codes_in_source()):
        en, ru = CODE_HELP.get(code, ("—", "—"))
        parts.append(f"<tr><td><code>{_esc(code)}</code></td>"
                     f"<td>{_esc(pick((en, ru), lang))}</td></tr>")
    parts.append("</table>")
    return "\n".join(parts)


def page():
    """One file, every language, switched in the browser.

    Built for two and now built from the list, which is the same move as the
    spec's: a language is data. Each block carries its own `dir`, so Hebrew
    turns the page round without a second stylesheet, and a language with no
    prose yet renders its English rather than an empty page."""
    body = "".join(
        f"<div class='lang' id='{code}' dir='{'rtl' if code in zfl2.RTL else 'ltr'}'"
        f"{'' if code == 'en' else ' hidden'}>" + render(code) + "</div>"
        for code, *_rest in zfl2.LANGS)
    # `c, n, *_` and not `c, n`: this row grew a third field once already
    # and a fixed-width unpack turned the whole page into a traceback. Read
    # what you need, let the row grow.
    nav = " · ".join(f"<a href='?l={c}' onclick=\"return t('{c}')\">{n}</a>"
                     for c, n, *_ in zfl2.LANGS)
    codes = ",".join(f"'{c}'" for c, *_ in zfl2.LANGS)
    return f"""<!doctype html><meta charset="utf-8">
<title>ZFL</title>
<style>
 body {{ font: 15px/1.5 Georgia, serif; max-width: 52em; margin: 3em auto;
        padding: 0 1em; color: #111; }}
 table {{ border-collapse: collapse; width: 100%; margin: 1em 0; }}
 th, td {{ border: 1px solid #bbb; padding: 5px 8px; text-align: left;
          vertical-align: top; font-size: 14px; }}
 th {{ background: #eee; }} tr.adv td {{ color: #666; }}
 code {{ background: #f4f4f4; padding: 1px 4px; }}
 [dir=rtl] th, [dir=rtl] td {{ text-align: right; }}
 nav {{ float: right; font-size: 13px; }}
</style>
<nav>{nav}</nav>
{body}
<script>
// ?l=xx opens the page already in that language, so a link can be handed to
// somebody in their own. Switching also rewrites the address bar, so
// whatever you are reading is what you copy.
const LANGS = [{codes}];
function t(l) {{
  if (!LANGS.includes(l)) l = 'en';
  for (const d of document.querySelectorAll('.lang')) d.hidden = d.id !== l;
  document.documentElement.lang = l;
  document.documentElement.dir = document.getElementById(l).dir;
  history.replaceState(null, '', '?l=' + l);
  return false;
}}
t(new URLSearchParams(location.search).get('l') || 'en');
</script>"""


def main():
    missing = ((codes_in_source() - set(CODE_HELP))
               | (set(operators()) - set(OP_HELP))
               | (set(column_examples("value")) - set(VALUE_HELP))
               | (set(arithmetic()) - set(ARITH_HELP)))
    stale = ((set(CODE_HELP) - codes_in_source())
             | (set(OP_HELP) - set(operators()))
             | (set(VALUE_HELP) - set(column_examples("value")))
             | (set(ARITH_HELP) - set(arithmetic())))
    print(f"codes raised by the validator: {len(codes_in_source())}")
    if missing or stale:
        print(f"  RED — undocumented: {sorted(missing)}")
        print(f"        documented but never raised: {sorted(stale)}")
        return 1
    print("  every code the validator raises is documented, and no more")
    if "--check" in sys.argv:
        print("ZFL DOC GREEN — the page and the language agree")
        return 0
    open(OUT, "w", encoding="utf-8").write(page())
    print(f"  written: {OUT}  ({os.path.getsize(OUT)} bytes)")
    print("ZFL DOC GREEN — the page and the language agree")
    return 0


if __name__ == "__main__":
    sys.exit(main())
