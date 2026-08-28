// ZTL Studio v2 — the table, built from the spec the validator enforces.
//
// This file knows no column names, no statuses, no options and no labels.
// It asks /api/formspec and draws what it is told, so the language lives in
// one place (tool/zfl2.py) and the front-end cannot drift from it. The only
// thing hard-coded here is the handful of words belonging to the CHROME —
// buttons and headings that are not part of the language.

const UI = {
  en: { advanced: "advanced", reference: "what is ZFL? (the language)", addrow: "add a row",
        run: "run", claim: "claim", remove: "remove this row",
        nothing: "nothing to show yet — fill a row and press run",
        applies: "instruments that had something to say",
        passport: "passports", numeric: "the numeric floor",
        epoch: "the world's clock", unredeemable: "this credit will never be redeemed", event: "event", expires: "expires with it", before: "before", after: "after", survives: "the conclusion survived", fell: "the conclusion did NOT survive", 
        demoted: "demoted to unverified — ground outside the document's list:", 
        receipt: "receipt", epoch: "epoch", registryf: "registry (names)", ancestors: "ancestors", undeclared: "not declared", 
        judge: "the judge", ledger: "the ledger",
        component: "component", kind: "passport", detail: "details",
        disposition: "disposition", cures: "what would settle it",
        sheet: "assembled sheet", verdict: "verdict", grade: "warranty",
        weak: "weak links", claims: "claims", brackets: "trust brackets",
        assumed: "assumed and unverifiable", eg: "e.g. ",
        solved: "solved", value: "value", from: "derived from",
        prov: "provenance", still: "still a box",
        needone: "the question does not fix a number: say any ONE of these "
                 + "and the rest follow —",
        needmore: "the question does not fix a number, and one more fact "
                  + "would not be enough",
        examples: "examples", send: "ask", commentary: "in plain language",
        askph: "describe the question in your own words…",
        thinking_note: "the verdict above is already complete — this is the model catching up",
        thinking: "filling the table…", pick: "— pick —",
        aioff: "no model key — the table and the verdict work without it",
        ownai: "use my own AI", keyph: "paste your API key",
        keysave: "use it", keyclear: "back to the free AI",
        keynote: "The key is kept in this browser tab only, for this session, "
                 + "and is sent to this server solely to call the provider "
                 + "you picked. Nothing is written to disk. Closing the tab "
                 + "forgets it.",
        keyon: "your own AI is in use", keyoff: "using the free AI",
        limit: "The free AI is used up (20 requests per 10 minutes per "
               + "visitor). Press \u00abuse my own AI\u00bb above to carry on "
               + "with your own key \u2014 or keep working without it: the "
               + "table and the verdict never needed the AI." },
  ru: { advanced: "дополнительно", reference: "что такое ZFL? (язык)",
        addrow: "добавить строку", run: "запустить", claim: "утверждение",
        remove: "убрать строку",
        nothing: "пока нечего показывать — заполните строку и запустите",
        applies: "приборы, которым было что сказать",
        passport: "паспорта", numeric: "числовой пол",
        epoch: "часы мира", unredeemable: "этот кредит не погасят никогда", event: "событие", expires: "вместе с ним истекает", before: "до", after: "после", survives: "вывод пережил", fell: "вывод НЕ пережил", 
        demoted: "разжаловано в непроверенное — основание вне списка документа:", 
        receipt: "квитанция", epoch: "эпоха", registryf: "реестр (имён)", ancestors: "предки", undeclared: "не объявлено", 
        judge: "судья", ledger: "тетрадь",
        component: "компонент", kind: "паспорт", detail: "подробности",
        disposition: "диспозиция", cures: "что это решит",
        sheet: "собранный лист", verdict: "вердикт", grade: "гарантия",
        weak: "слабые звенья", claims: "притязания", brackets: "вилки доверия",
        assumed: "принято на веру и непроверяемо", eg: "напр. ",
        solved: "решено", value: "величина", from: "выведено из",
        prov: "происхождение", still: "ещё коробка",
        needone: "вопрос не определяет числа: назовите ЛЮБОЕ одно из этих — "
                 + "остальные встанут сами:",
        needmore: "вопрос не определяет числа, и одного факта не хватит",
        examples: "примеры", send: "спросить", commentary: "по-человечески",
        askph: "опишите вопрос своими словами…",
        thinking_note: "вердикт выше уже готов — это модель договаривает",
        thinking: "заполняю таблицу…", pick: "— выберите —",
        aioff: "ключа модели нет — таблица и вердикт работают и без неё",
        ownai: "свой ИИ", keyph: "вставьте свой API-ключ",
        keysave: "использовать", keyclear: "вернуться к бесплатному",
        keynote: "Ключ хранится только в этой вкладке браузера и только на "
                 + "текущий сеанс, а на сервер уходит единственно ради вызова "
                 + "выбранного вами провайдера. На диск ничего не пишется. "
                 + "Закроете вкладку — он забудется.",
        keyon: "работает ваш ИИ", keyoff: "работает бесплатный ИИ",
        limit: "Бесплатный ИИ исчерпан (20 запросов за 10 минут на "
               + "посетителя). Нажмите «свой ИИ» вверху и продолжите со "
               + "своим ключом — или работайте без него: таблица и вердикт "
               + "в ИИ никогда не нуждались." },
  uk: { advanced: "додатково", reference: "що таке ZFL? (мова)",
        addrow: "додати рядок", run: "запустити", claim: "твердження",
        remove: "прибрати рядок",
        nothing: "поки нічого показувати — заповніть рядок і запустіть",
        applies: "прилади, яким було що сказати",
        passport: "паспорти", numeric: "числова підлога",
        epoch: "годинник світу", unredeemable: "цей кредит не погасять ніколи", event: "подія", expires: "разом із нею спливає", before: "до", after: "після", survives: "висновок пережив", fell: "висновок НЕ пережив", 
        demoted: "розжаловано в неперевірене — підстава поза списком документа:", 
        receipt: "квитанція", epoch: "епоха", registryf: "реєстр (імен)", ancestors: "предки", undeclared: "не оголошено", 
        judge: "суддя", ledger: "зошит",
        component: "компонент", kind: "паспорт", detail: "подробиці",
        disposition: "диспозиція", cures: "що це вирішить",
        sheet: "зібраний аркуш", verdict: "вердикт", grade: "гарантія",
        weak: "слабкі ланки", claims: "домагання", brackets: "вилки довіри",
        assumed: "прийнято на віру і неперевірне", eg: "напр. ",
        solved: "розв'язано", value: "величина", from: "виведено з",
        prov: "походження", still: "ще коробка",
        needone: "питання не визначає числа: назвіть БУДЬ-ЯКЕ одне з цих — "
                 + "решта стане сама:",
        needmore: "питання не визначає числа, і одного факту не вистачить",
        examples: "приклади", send: "запитати", commentary: "по-людськи",
        askph: "опишіть питання своїми словами…",
        thinking_note: "вердикт вище вже готовий — це модель договорює",
        thinking: "заповнюю таблицю…", pick: "— оберіть —",
        aioff: "ключа моделі немає — таблиця і вердикт працюють і без неї",
        ownai: "свій ШІ", keyph: "вставте свій API-ключ",
        keysave: "використати", keyclear: "повернутись до безкоштовного",
        keynote: "Ключ зберігається лише в цій вкладці браузера й лише на "
                 + "поточний сеанс, а на сервер іде єдино заради виклику "
                 + "обраного вами провайдера. На диск нічого не пишеться. "
                 + "Закриєте вкладку — він забудеться.",
        keyon: "працює ваш ШІ", keyoff: "працює безкоштовний ШІ",
        limit: "Безкоштовний ШІ вичерпано (20 запитів за 10 хвилин на "
               + "відвідувача). Натисніть «свій ШІ» вгорі й продовжте зі "
               + "своїм ключем — або працюйте без нього: таблиця і вердикт "
               + "у ШІ ніколи не потребували." },
  he: { advanced: "מתקדם", reference: "מהי ZFL? (השפה)",
        addrow: "הוספת שורה", run: "הרצה", claim: "הטענה",
        remove: "הסרת השורה",
        nothing: "עדיין אין מה להראות — מלאו שורה והריצו",
        applies: "הכלים שהיה להם מה לומר",
        passport: "דרכונים", numeric: "הרצפה המספרית",
        epoch: "שעון העולם", unredeemable: "אשראי זה לעולם לא ייפרע", event: "אירוע", expires: "פג יחד איתו", before: "לפני", after: "אחרי", survives: "המסקנה שרדה", fell: "המסקנה לא שרדה", 
        demoted: "הורד ללא־מאומת — אסמכתא מחוץ לרשימת המסמך:", 
        receipt: "קבלה", epoch: "תקופה", registryf: "מרשם (שמות)", ancestors: "אבות", undeclared: "לא הוצהר", 
        judge: "השופט", ledger: "הפנקס",
        component: "רכיב", kind: "דרכון", detail: "פרטים",
        disposition: "מצב", cures: "מה יכריע את זה",
        sheet: "הגיליון שהורכב", verdict: "פסק", grade: "ערובה",
        weak: "חוליות חלשות", claims: "תביעות", brackets: "תחומי אמון",
        assumed: "נלקח באמון ואינו ניתן לאימות", eg: "לדוגמה ",
        solved: "נפתר", value: "ערך", from: "נגזר מ־",
        prov: "מקור", still: "עדיין קופסה",
        needone: "השאלה אינה קובעת מספר: אמרו אחד כלשהו מאלה — "
                 + "והשאר ייקבע מעצמו:",
        needmore: "השאלה אינה קובעת מספר, ועובדה אחת נוספת לא תספיק",
        examples: "דוגמאות", send: "שאלו", commentary: "בשפה פשוטה",
        askph: "תארו את השאלה במילים שלכם…",
        thinking_note: "הפסק שלמעלה כבר מוכן — זה המודל משלים",
        thinking: "ממלא את הטבלה…", pick: "— בחרו —",
        aioff: "אין מפתח למודל — הטבלה והפסק עובדים גם בלעדיו",
        ownai: "ה־AI שלי", keyph: "הדביקו את מפתח ה־API שלכם",
        keysave: "להשתמש", keyclear: "חזרה ל־AI החינמי",
        keynote: "המפתח נשמר רק בלשונית הזו ורק לסשן הנוכחי, ונשלח לשרת אך " 
                 + "ורק כדי לקרוא לספק שבחרתם. דבר אינו נכתב לדיסק. סגירת "
                 + "הלשונית מוחקת אותו.",
        keyon: "ה־AI שלכם פועל", keyoff: "ה־AI החינמי פועל",
        limit: "ה־AI החינמי מוצה (20 בקשות ל־10 דקות למבקר). לחצו על "
               + "«ה־AI שלי» למעלה והמשיכו עם מפתח משלכם — או עבדו בלעדיו: "
               + "הטבלה והפסק מעולם לא נזקקו ל־AI." },
  de: { advanced: "erweitert", reference: "Was ist ZFL? (die Sprache)",
        addrow: "Zeile hinzufügen", run: "ausführen", claim: "Behauptung",
        remove: "diese Zeile entfernen",
        nothing: "noch nichts zu zeigen — Zeile ausfüllen und ausführen",
        applies: "Instrumente, die etwas zu sagen hatten",
        passport: "Pässe", numeric: "die Zahlenebene",
        epoch: "die Uhr der Welt", unredeemable: "dieser Kredit wird nie eingelöst", event: "Ereignis", expires: "erlischt damit", before: "davor", after: "danach", survives: "der Schluss hat überlebt", fell: "der Schluss hat NICHT überlebt", 
        demoted: "auf ungeprüft herabgestuft — Grundlage nicht in der Liste:", 
        receipt: "Quittung", epoch: "Epoche", registryf: "Register (Namen)", ancestors: "Vorfahren", undeclared: "nicht angegeben", 
        judge: "der Richter", ledger: "das Buch",
        component: "Komponente", kind: "Pass", detail: "Einzelheiten",
        disposition: "Befund", cures: "was es entscheiden würde",
        sheet: "zusammengesetztes Blatt", verdict: "Urteil", grade: "Gewähr",
        weak: "schwache Glieder", claims: "Ansprüche", brackets: "Vertrauensspannen",
        assumed: "auf Treu und Glauben, nicht prüfbar", eg: "z. B. ",
        solved: "gelöst", value: "Wert", from: "abgeleitet aus",
        prov: "Herkunft", still: "noch eine Schachtel",
        needone: "die Frage legt keine Zahl fest: nennen Sie IRGENDEINE davon — "
                 + "der Rest folgt:",
        needmore: "die Frage legt keine Zahl fest, und eine weitere Tatsache "
                  + "würde nicht reichen",
        examples: "Beispiele", send: "fragen", commentary: "in Klartext",
        askph: "beschreiben Sie die Frage in eigenen Worten…",
        thinking_note: "das Urteil oben steht bereits — das Modell holt nur auf",
        thinking: "fülle die Tabelle…", pick: "— wählen —",
        aioff: "kein Modellschlüssel — Tabelle und Urteil arbeiten auch ohne",
        ownai: "eigene KI", keyph: "Ihren API-Schlüssel einfügen",
        keysave: "verwenden", keyclear: "zurück zur kostenlosen KI",
        keynote: "Der Schlüssel bleibt nur in diesem Browser-Tab und nur für "
                 + "diese Sitzung; an den Server geht er einzig, um den von "
                 + "Ihnen gewählten Anbieter aufzurufen. Nichts wird auf die "
                 + "Festplatte geschrieben. Tab zu — Schlüssel vergessen.",
        keyon: "Ihre eigene KI ist aktiv", keyoff: "die kostenlose KI ist aktiv",
        limit: "Die kostenlose KI ist aufgebraucht (20 Anfragen pro 10 Minuten "
               + "je Besucher). Klicken Sie oben auf «eigene KI» und machen Sie "
               + "mit Ihrem Schlüssel weiter — oder arbeiten Sie ohne: Tabelle "
               + "und Urteil haben die KI nie gebraucht." },
  fr: { advanced: "avancé", reference: "qu'est-ce que ZFL ? (le langage)",
        addrow: "ajouter une ligne", run: "exécuter", claim: "affirmation",
        remove: "retirer cette ligne",
        nothing: "rien à montrer pour l'instant — remplissez une ligne et exécutez",
        applies: "les instruments qui avaient quelque chose à dire",
        passport: "passeports", numeric: "le socle numérique",
        epoch: "l'horloge du monde", unredeemable: "ce crédit ne sera jamais remboursé", event: "événement", expires: "expire avec lui", before: "avant", after: "après", survives: "la conclusion a survécu", fell: "la conclusion n'a PAS survécu", 
        demoted: "rétrogradé en non vérifié — fondement hors de la liste :", 
        receipt: "reçu", epoch: "époque", registryf: "registre (noms)", ancestors: "ancêtres", undeclared: "non déclaré", 
        judge: "le juge", ledger: "le registre",
        component: "composant", kind: "passeport", detail: "détails",
        disposition: "disposition", cures: "ce qui trancherait",
        sheet: "feuille assemblée", verdict: "verdict", grade: "garantie",
        weak: "maillons faibles", claims: "prétentions", brackets: "fourchettes de confiance",
        assumed: "admis sur parole et invérifiable", eg: "p. ex. ",
        solved: "résolu", value: "valeur", from: "dérivé de",
        prov: "provenance", still: "encore une boîte",
        needone: "la question ne fixe aucun nombre : donnez N'IMPORTE LEQUEL "
                 + "de ceux-ci — le reste suivra :",
        needmore: "la question ne fixe aucun nombre, et un fait de plus ne "
                  + "suffirait pas",
        examples: "exemples", send: "demander", commentary: "en clair",
        askph: "décrivez la question avec vos mots…",
        thinking_note: "le verdict ci-dessus est déjà complet — le modèle rattrape",
        thinking: "je remplis le tableau…", pick: "— choisir —",
        aioff: "pas de clé de modèle — le tableau et le verdict marchent sans",
        ownai: "mon IA", keyph: "collez votre clé API",
        keysave: "l'utiliser", keyclear: "revenir à l'IA gratuite",
        keynote: "La clé ne reste que dans cet onglet et seulement pour cette "
                 + "session ; elle ne part vers le serveur que pour appeler le "
                 + "fournisseur que vous avez choisi. Rien n'est écrit sur "
                 + "disque. Fermez l'onglet et elle est oubliée.",
        keyon: "votre IA est active", keyoff: "l'IA gratuite est active",
        limit: "L'IA gratuite est épuisée (20 requêtes par 10 minutes et par "
               + "visiteur). Cliquez sur «mon IA» en haut et continuez avec "
               + "votre clé — ou travaillez sans : le tableau et le verdict "
               + "n'ont jamais eu besoin de l'IA." },
  es: { advanced: "avanzado", reference: "¿qué es ZFL? (el lenguaje)",
        addrow: "añadir fila", run: "ejecutar", claim: "afirmación",
        remove: "quitar esta fila",
        nothing: "todavía nada que mostrar — rellene una fila y ejecute",
        applies: "instrumentos que tuvieron algo que decir",
        passport: "pasaportes", numeric: "el suelo numérico",
        epoch: "el reloj del mundo", unredeemable: "este crédito no se saldará nunca", event: "evento", expires: "expira con él", before: "antes", after: "después", survives: "la conclusión sobrevivió", fell: "la conclusión NO sobrevivió", 
        demoted: "degradado a no verificado — fundamento fuera de la lista:", 
        receipt: "recibo", epoch: "época", registryf: "registro (nombres)", ancestors: "ancestros", undeclared: "no declarado", 
        judge: "el juez", ledger: "el registro",
        component: "componente", kind: "pasaporte", detail: "detalles",
        disposition: "disposición", cures: "qué lo resolvería",
        sheet: "hoja compuesta", verdict: "veredicto", grade: "garantía",
        weak: "eslabones débiles", claims: "pretensiones", brackets: "horquillas de confianza",
        assumed: "aceptado de palabra y no verificable", eg: "p. ej. ",
        solved: "resuelto", value: "valor", from: "derivado de",
        prov: "procedencia", still: "todavía una caja",
        needone: "la pregunta no fija ningún número: diga CUALQUIERA de "
                 + "estos — el resto se sigue:",
        needmore: "la pregunta no fija ningún número, y un dato más no bastaría",
        examples: "ejemplos", send: "preguntar", commentary: "en lenguaje llano",
        askph: "describa la pregunta con sus palabras…",
        thinking_note: "el veredicto de arriba ya está completo — el modelo va detrás",
        thinking: "rellenando la tabla…", pick: "— elija —",
        aioff: "sin clave de modelo — la tabla y el veredicto funcionan igual",
        ownai: "mi IA", keyph: "pegue su clave API",
        keysave: "usarla", keyclear: "volver a la IA gratuita",
        keynote: "La clave se guarda solo en esta pestaña y solo para esta "
                 + "sesión; al servidor va únicamente para llamar al proveedor "
                 + "que usted eligió. Nada se escribe en disco. Al cerrar la "
                 + "pestaña se olvida.",
        keyon: "su propia IA está en uso", keyoff: "la IA gratuita está en uso",
        limit: "La IA gratuita se agotó (20 peticiones por 10 minutos por "
               + "visitante). Pulse «mi IA» arriba y siga con su propia clave "
               + "— o trabaje sin ella: la tabla y el veredicto nunca "
               + "necesitaron la IA." },
};

let LANG = new URLSearchParams(location.search).get("l") || "en";
let SPEC = null;
let ROWS = [];

const $ = id => document.getElementById(id);
// A word that has no translation yet shows its English rather than its key.
// The same rule as the spec's: a half-translated language works.
const t = k => (UI[LANG] && UI[LANG][k]) || UI.en[k] || k;

function esc(s) {
  return String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;")
                  .replace(/"/g, "&quot;").replace(/'/g, "&#39;");
}

async function loadSpec() {
  const r = await fetch(`/api/formspec?l=${LANG}`);
  SPEC = await r.json();
}

// ---------------------------------------------------------------- the grid
// ---------------------------------------------------- suggested ground names
// The spec says WHICH column offers names, under which statuses, and what to
// call them; this file still knows none of that by name.
// A sentinel, never a ground: parentheses are not legal in a name, so
// this value cannot collide with anything a person could pick or type.
const OWN = "(own)";

function suggestState(col, row) {
  const s = col.suggest;
  if (!s || row["_own_" + col.key]) return null;
  return s.when_status.includes(row.status || "") ? s : null;
}

function usedGrounds(col, skip) {
  const out = [];
  ROWS.forEach((r, j) => {
    const v = (r[col.key] || "").trim();
    if (j !== skip && v && !out.includes(v)) out.push(v);
  });
  return out;
}

// The next name nobody is using yet. Not "count the rows and offer ten" —
// offering ten meaningless items is the same confusion in a new shape. Show
// what is already in play, plus one fresh one, and the list grows only as
// fast as the ledger actually needs it.
function freshGround(s, used) {
  for (let n = 1; ; n++) if (!used.includes(s.prefix + n)) return s.prefix + n;
}

function groundLabel(s, value) {
  const m = value.startsWith(s.prefix) && /^\d+$/.test(value.slice(s.prefix.length));
  return m ? s.label.replace("%d", value.slice(s.prefix.length)) : value;
}

function widget(col, row, i) {
  const v = row[col.key] ?? col.default ?? "";
  const sg = suggestState(col, row);
  if (sg) {
    const used = usedGrounds(col, i);
    const list = used.slice();
    if (v && !list.includes(v)) list.unshift(v);
    // A fresh name is only worth offering when there is another row to
    // share it with or differ from. With a single row, renaming ground-1 to
    // ground-2 says nothing, and an option that says nothing is the same
    // noise this change set out to remove.
    if (ROWS.length > 1) {
      const fresh = freshGround(sg, list);
      if (!list.includes(fresh)) list.push(fresh);
    }
    // Generated names read as a sequence, so they must be offered as one:
    // "Ground 2, Ground 1, Ground 3" is a list a person has to re-sort in
    // their head. Names of their own keep their place at the front.
    const num = g => g.startsWith(sg.prefix) && /^\d+$/.test(g.slice(sg.prefix.length))
                     ? +g.slice(sg.prefix.length) : -1;
    list.sort((a, b) => num(a) - num(b));
    const opts = list.map(g =>
      `<option value="${esc(g)}"${g === v ? " selected" : ""}>` +
      `${esc(groundLabel(sg, g))}</option>`).join("");
    return `<select data-i="${i}" data-k="${esc(col.key)}">${opts}` +
           `<option value="${esc(OWN)}">${esc(sg.own)}</option></select>`;
  }
  // a cell whose meaning depends on another cell must SAY so, per row:
  // `inv-17` and `~Tr(L)` are not the same kind of thing, and the status
  // is what decides which one this cell wants
  const mode = col.help_when && col.help_when[row.status || ""];
  if (col.widget === "choice") {
    const opts = col.options.map(o =>
      `<option value="${esc(o.value)}"${o.value === v ? " selected" : ""}>` +
      `${esc(o.label)}</option>`).join("");
    return `<select data-i="${i}" data-k="${esc(col.key)}">${opts}</select>`;
  }
  if (col.widget === "bool") {
    return `<input type="checkbox" data-i="${i}" data-k="${esc(col.key)}"` +
           `${v ? " checked" : ""}>`;
  }
  // "e.g." matters: a bare `1500` in an empty cell reads as a value that
  // is already there, which is exactly how the first screenshot looked
  const hint = mode ? mode.eg : (col.eg || [])[0];
  const title = mode ? mode.help : col.help;
  return `<input type="text" data-i="${i}" data-k="${esc(col.key)}" ` +
         `value="${esc(v)}" title="${esc(title)}" ` +
         `${mode && !mode.eg ? 'class="dim" ' : ""}` +
         `placeholder="${hint ? esc(t("eg") + hint) : ""}">`;
}

function drawGrid() {
  const head = SPEC.columns.map(c =>
    `<th class="${c.advanced ? "adv" : ""}">${esc(c.label)}` +
    `<small>${esc(c.help)}</small></th>`).join("");
  const body = ROWS.map((row, i) =>
    "<tr>" + SPEC.columns.map(c =>
      `<td class="${c.advanced ? "adv" : ""}">${widget(c, row, i)}</td>`
    ).join("") +
    `<td><button class="rowbtn" data-del="${i}" title="${esc(t("remove"))}">` +
    `×</button></td></tr>`).join("");
  $("grid").innerHTML = `<tr>${head}<th></th></tr>${body}`;
}

function collect() {
  // `_own_*` is the form remembering that this cell was switched to free
  // text. It is interface state, not part of the document, and the runner
  // must never see a key the language does not have.
  const clean = r => Object.fromEntries(
    Object.entries(r).filter(([k]) => !k.startsWith("_")));
  return { rows: ROWS.filter(r => (r.name || "").trim()).map(clean),
           grounds: ($("grounds") || {}).value || "",
           claim: $("claim").value };
}

// --------------------------------------------------------------- reporting
function panel(title, inner) {
  return `<div class="panel"><h3>${esc(title)}</h3>${inner}</div>`;
}

function table(headers, rows) {
  return "<table><tr>" + headers.map(h => `<th>${esc(h)}</th>`).join("") +
    "</tr>" + rows.map(r => "<tr>" + r.map(c => `<td>${c}</td>`).join("") +
    "</tr>").join("") + "</table>";
}

function verdictSpan(v) {
  return `<span class="v-${esc(v)}">${esc(v)}</span>`;
}

function showIssues(issues) {
  $("issues").innerHTML = (issues || []).map(i =>
    `<div class="${esc(i.level)}">${esc(i.code)} · ${esc(i.where)} — ` +
    `${esc(i.hint)}</div>`).join("");
  document.querySelectorAll(".grid td").forEach(td =>
    td.classList.remove("err"));
}

function showReport(r) {
  const out = [];
  const rep = r.report || {};
  if (rep.passport) {
    out.push(panel(t("passport"), table(
      [t("component"), t("kind"), t("detail")],
      rep.passport.map(p => [esc(p.component.join(", ")),
                             verdictSpan(p.kind), esc(p.detail)]))));
  }
  if (rep.numeric) {
    const sv = Object.entries(rep.numeric.solved || {});
    const solvedTable = sv.length ? table(
      [t("solved"), t("value"), t("prov"), t("from")],
      sv.map(([n, v]) => [esc(n),
        `<b>${esc(v.lo === v.hi ? v.lo : `[${v.lo}, ${v.hi}]`)}</b>` +
        (v.pinned ? "" : ` <span class="muted">${esc(t("still"))}</span>`),
        verdictSpan(v.prov === "earned" ? "EARNED" : v.prov),
        esc((v.from || []).join(", ") || "—")])) : "";
    const miss = rep.numeric.missing;
    const missLine = !miss ? ""
      : miss.needs === 1
        ? `<p><b>${esc(t("needone"))}</b> ${esc(miss.any_of.join(" · "))}</p>`
        : `<p><b>${esc(t("needmore"))}</b></p>`;
    out.push(panel(t("numeric"),
      `<p>${verdictSpan(rep.numeric.disposition)}</p>` + missLine + solvedTable +
      (rep.numeric.next_check.length
        ? `<p class="muted">${t("cures")}: ` +
          esc(rep.numeric.next_check.join(" · ")) + "</p>" : "") +
      `<p class="muted">${t("sheet")}: <code>` +
      esc(rep.numeric.sheet) + "</code></p>"));
  }
  if (rep.judge) {
    // A CREDIT THAT CANNOT BE REDEEMED must not read as an ordinary one.
    // "until-verification" is a promise that checking is possible, and on a
    // dead ring that promise is false — the passport knew, the judge did
    // not, and the reader was sent to verify the liar (2026-08-28).
    const dead = rep.judge.credit === "UNREDEEMABLE"
      ? `<p><b class="v-F">${esc(t("unredeemable"))}</b> ` +
        `<span class="muted">${esc((rep.judge.unredeemable || []).join(", "))}` +
        `</span></p>`
      : "";
    out.push(panel(t("judge"),
      `<p>${t("verdict")}: ${verdictSpan(rep.judge.verdict)} · ` +
      `${t("grade")}: ${esc(rep.judge.grade)}</p>` + dead +
      (rep.judge.unverified.length
        ? `<p class="muted">${t("weak")}: ` +
          esc(rep.judge.unverified.join(", ")) + "</p>" : "")));
  }
  if (r.report && r.report.demoted_grounds) {
    out.unshift(`<p><b class="v-F">${esc(t("demoted"))}</b> ` +
                `<span class="muted">${esc(r.report.demoted_grounds.join(", "))}` +
                `</span></p>`);
  }
  if (rep.receipt) {
    // Квитанция ВСЕГДА, и НЕОБЪЯВЛЕННОЕ показано словом, а не пропуском:
    // читатель должен видеть, чего ей недостаёт, а не догадываться.
    const q = rep.receipt, нет = `<span class="v-F">${esc(t("undeclared"))}</span>`;
    out.push(panel(t("receipt"),
      `<p><code>${esc(q.digest)}</code></p>` +
      `<p class="muted">${esc(t("epoch"))}: ` +
      (q.epoch ? esc(q.epoch) : нет) + " · " +
      `${esc(t("registryf"))}: ` +
      (q.registry ? esc(String(q.registry.size)) : нет) + " · " +
      `${esc(t("ancestors"))}: ` +
      (q.derived_from ? esc(Object.keys(q.derived_from).join(", ")) : нет) +
      "</p>"));
  }
  if (rep.epoch) {
    out.push(panel(t("epoch"), table(
      [t("event"), t("expires"), t("before"), t("after"), ""],
      rep.epoch.map(e => [
        esc(e.event), esc(e.expires.join(", ")),
        verdictSpan(e.before.verdict) + ` <span class="muted">` +
          esc(e.before.grade) + "</span>",
        verdictSpan(e.after.verdict) + ` <span class="muted">` +
          esc(e.after.grade) + "</span>",
        e.survives ? esc(t("survives"))
                   : `<b class="v-F">${esc(t("fell"))}</b>`]))));
  }
  if (rep.ledger) {
    const rows = Object.entries(rep.ledger.claims).map(([k, v]) =>
      [esc(k), verdictSpan(v.disposition),
       esc(Object.values(v.assurance).join(" · "))]);
    out.push(panel(t("ledger"),
      table([t("claims"), t("disposition"), ""], rows) +
      `<p class="muted">${t("brackets")}: ` +
      esc(JSON.stringify(rep.ledger.brackets)) + "</p>" +
      `<p class="muted">${t("assumed")}: ` +
      esc(rep.ledger.naming.assumption) + "</p>"));
  }
  if (!out.length) out.push(`<p class="muted">${esc(t("nothing"))}</p>`);
  if (r.applies) {
    const on = Object.entries(r.applies).filter(([, v]) => v).map(([k]) => t(k));
    out.unshift(`<p class="muted">${esc(t("applies"))}: ` +
                esc(on.join(" · ") || "—") + "</p>");
  }
  $("report").innerHTML = out.join("");
}

// ------------------------------------------------------- examples and chat
let EX = null;

async function loadExamples() {
  EX = await fetch(`/api/v2examples?l=${LANG}`).then(r => r.json());
  const k = $("exkind");
  k.innerHTML = `<option value="">${esc(t("pick"))}</option>` +
    EX.kinds.map(x => `<option value="${esc(x.key)}">${esc(x.label)}</option>`)
      .join("");
  fillItems("");
}

function fillItems(kind) {
  const items = EX.items.filter(i => !kind || i.kind === kind);
  $("exitem").innerHTML = `<option value="">${esc(t("pick"))}</option>` +
    items.map((i, n) => `<option value="${n}">${esc(i.label)}</option>`)
      .join("");
  $("exitem").disabled = !kind;
}

function loadExample(kind, n) {
  const items = EX.items.filter(i => !kind || i.kind === kind);
  const item = items[n];
  if (!item) return;
  ROWS = JSON.parse(JSON.stringify(item.doc.rows));
  $("claim").value = item.doc.claim || "";
  // the QUESTION goes into the chat, so the commentary below has something
  // to be an answer TO. Not everyone knows what "Jourdain's postcard" is,
  // and a verdict with no question above it explains nothing.
  $("chat").innerHTML = "";
  HISTORY = [];
  if (item.ask) {
    addMsg("user", item.ask);
    HISTORY = [{ role: "user", content: item.ask }];
  }
  drawGrid();
  run();
}

function addMsg(role, text) {
  const d = document.createElement("div");
  d.className = "msg " + role;
  d.textContent = text;
  $("chat").appendChild(d);
  $("chat").scrollTop = $("chat").scrollHeight;
  return d;
}

let HISTORY = [];

async function ask() {
  const q = $("ask").value.trim();
  if (!q) return;
  $("ask").value = "";
  addMsg("user", q);
  HISTORY.push({ role: "user", content: q });
  const pending = addMsg("sys", t("thinking"));
  const r = await fetch("/api/v2fill", {
    method: "POST", headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ history: HISTORY, lang: LANG, cfg: cfg() }),
  }).then(x => x.json());
  pending.remove();
  if (!r.ok) { addMsg("sys", aiError(r)); return; }
  ROWS = r.doc.rows || [];
  $("claim").value = r.doc.claim || "";
  HISTORY.push({ role: "assistant", content: JSON.stringify(r.doc) });
  drawGrid();
  run();
}


// ------------------------------------------------------ your own model key
// The server already refuses past 20 free calls per ten minutes and its
// refusal used to say "enter your own key in ⚙ Model" — a control that
// existed in v1 and was never rebuilt here, so the message named a button
// nobody could find. This is that button.
//
// SESSION ONLY, and that is not a slogan: the key lives in sessionStorage,
// which the browser drops when the tab closes, and it is never sent to
// /api/savekey (which is disabled on the public instance anyway). It travels
// with each AI request because that is the only way the server can call the
// provider on the user's behalf, and the panel says so in plain words rather
// than leaving the reader to assume.
let PROVIDERS = [];

function cfg() {
  try {
    const raw = sessionStorage.getItem("ztl_cfg");
    return raw ? JSON.parse(raw) : null;
  } catch (e) { return null; }
}

function cfgLabel() {
  const c = cfg();
  $("ownai").textContent = c && c.key
    ? `${t("ownai")} · ${t("keyon")}` : t("ownai");
}

async function keyPanel() {
  const p = $("keypanel");
  if (!p.hidden) { p.hidden = true; return; }
  if (!PROVIDERS.length) {
    const r = await fetch("/api/providers", { method: "POST",
      headers: { "Content-Type": "application/json" }, body: "{}" })
      .then(x => x.json()).catch(() => ({ providers: [] }));
    PROVIDERS = r.providers || [];
  }
  const c = cfg() || {};
  const opts = PROVIDERS.map(pr =>
    `<option value="${esc(pr.provider)}"${pr.provider === c.provider ?
      " selected" : ""}>${esc(pr.label)}</option>`).join("");
  p.innerHTML =
    `<div class="keybox">` +
    `<select id="kprov">${opts}</select> ` +
    `<select id="kmodel"></select> ` +
    `<input id="kkey" type="password" placeholder="${esc(t("keyph"))}" ` +
    `value="${esc(c.key || "")}"> ` +
    `<button id="ksave">${esc(t("keysave"))}</button> ` +
    `<button id="kclear">${esc(t("keyclear"))}</button>` +
    `<div class="keynote">${esc(t("keynote"))}</div>` +
    `<div class="keynote"><a id="kconsole" target="_blank" rel="noopener"></a>` +
    `</div></div>`;
  p.hidden = false;
  const models = () => {
    const pr = PROVIDERS.find(x => x.provider === $("kprov").value);
    $("kmodel").innerHTML = (pr ? pr.models : []).map(m =>
      `<option value="${esc(m)}"${m === c.model ? " selected" : ""}>` +
      `${esc(m)}</option>`).join("");
    const a = $("kconsole");
    a.href = pr ? pr.console : "#";
    a.textContent = pr ? pr.console : "";
  };
  models();
  $("kprov").onchange = models;
  $("ksave").onclick = () => {
    sessionStorage.setItem("ztl_cfg", JSON.stringify({
      provider: $("kprov").value, model: $("kmodel").value,
      key: $("kkey").value.trim() }));
    p.hidden = true;
    cfgLabel();
  };
  $("kclear").onclick = () => {
    sessionStorage.removeItem("ztl_cfg");
    p.hidden = true;
    cfgLabel();
  };
}

// The server's refusal is a sentence in English written for v1. When it is
// the rate limit talking, say it in the reader's language and point at the
// control that now exists — and say, because it is true, that nothing they
// came for is blocked.
function aiError(r) {
  const raw = r.error || (r.issues || []).map(i => i.hint).join("; ");
  return /free-AI limit|limit reached/i.test(raw || "") ? t("limit") : raw;
}

async function commentary(doc, result) {
  // A PLACE IS TAKEN BEFORE THE ANSWER ARRIVES. The verdict appears at once
  // and the model's plain-language note lands seconds later, so without this
  // the page looks finished and then twitches. The panel says what is coming
  // and, in the same breath, that nothing is being waited FOR: the verdict
  // above it is already complete.
  const slot = document.createElement("div");
  slot.className = "panel comment pending";
  slot.innerHTML = `<h3>${esc(t("commentary"))}</h3>` +
                   `<p class="wait"><span class="aibar"></span>` +
                   `${esc(t("thinking_note"))}</p>`;
  $("report").appendChild(slot);
  const r = await fetch("/api/v2comment", {
    method: "POST", headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ doc, result, lang: LANG, cfg: cfg() }),
  }).then(x => x.json());
  if (!r.ok) {
    // a refusal is not silence: the reader is told, in their language, and
    // the limit message names the control that fixes it
    slot.classList.remove("pending");
    slot.innerHTML = `<h3>${esc(t("commentary"))}</h3>` +
                     `<p class="dim">${esc(aiError(r))}</p>`;
    return;
  }
  slot.classList.remove("pending");
  slot.innerHTML = `<h3>${esc(t("commentary"))}</h3><p>${esc(r.reply)}</p>`;
}

// ------------------------------------------------------------------ wiring
async function run() {
  const doc = collect();
  const r = await fetch("/api/v2run", {
    method: "POST", headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ doc }),
  }).then(x => x.json());
  showIssues(r.issues);
  if (!r.ok) { $("report").innerHTML = ""; return; }
  showReport(r);
  // the commentary is asked for AFTER the verdict exists, and never
  // stands between the core and the screen
  commentary(doc, r);
}

function chrome() {
  document.querySelectorAll("[data-t]").forEach(e =>
    e.textContent = t(e.dataset.t));
  document.querySelectorAll("[data-ph]").forEach(e =>
    e.placeholder = t(e.dataset.ph));
  $("claimlabel").textContent = t("claim");
  // Подпись поля берём ИЗ СПЕКИ, а не из словаря интерфейса: реестр —
  // часть языка, и его имя должно приходить оттуда же, откуда приходит
  // проверка. (Иначе подпись и правило разъедутся, как уже бывало.)
  const gspec = (SPEC.document || []).find(c => c.key === "grounds");
  if (gspec && $("groundslabel")) {
    $("groundslabel").textContent = gspec.label;
    $("groundslabel").title = gspec.help;
    if ($("grounds")) $("grounds").placeholder = (gspec.eg || [""])[0];
  }
  const sel = $("lang");
  sel.innerHTML = (SPEC.langs || [{ code: "en", label: "English" }]).map(l =>
    `<option value="${esc(l.code)}"${l.code === LANG ? " selected" : ""}>` +
    `${esc(l.label)}</option>`).join("");
  // Hebrew is not merely another column of strings: the page turns round.
  document.documentElement.dir = SPEC.rtl ? "rtl" : "ltr";
  $("ref").href = `/zfl?l=${LANG}`;
  $("home").href = `/?l=${LANG}`;
  cfgLabel();
  document.documentElement.lang = LANG;
}

function addRow() {
  const row = {};
  SPEC.columns.forEach(c => { if (c.default != null) row[c.key] = c.default; });
  ROWS.push(row);
  drawGrid();
}

document.addEventListener("input", e => {
  const i = e.target.dataset?.i;
  if (i == null) return;
  const k = e.target.dataset.k;
  ROWS[i][k] = e.target.type === "checkbox" ? e.target.checked : e.target.value;
  // "a name of my own" is not a ground, it is a request for the text box
  const own = SPEC.columns.find(c => c.key === k && c.suggest);
  if (own && ROWS[i][k] === OWN) {
    ROWS[i]["_own_" + k] = true;
    ROWS[i][k] = "";
    drawGrid();
    return;
  }
  // changing the status changes what the ground cell is asking for, so the
  // row is drawn again rather than left showing the previous question
  if (k === "status") { fillSuggested(i); drawGrid(); }
});

// A status that needs a ground gets one immediately, rather than a refusal
// the reader has to decode. This is the whole point of the change: the
// commonest error in the studio was raised against a row the person had
// filled in good faith.
function fillSuggested(i) {
  SPEC.columns.forEach(c => {
    const sg = suggestState(c, ROWS[i]);
    if (sg && !(ROWS[i][c.key] || "").trim())
      ROWS[i][c.key] = freshGround(sg, usedGrounds(c, i));
  });
}
document.addEventListener("click", e => {
  const d = e.target.dataset?.del;
  if (d != null) { ROWS.splice(+d, 1); drawGrid(); }
});
$("ownai").onclick = e => { e.preventDefault(); keyPanel(); };
$("addrow").onclick = addRow;
$("send").onclick = ask;
$("ask").onkeydown = e => { if (e.key === "Enter") ask(); };
$("exkind").onchange = e => fillItems(e.target.value);
$("exitem").onchange = e => loadExample($("exkind").value, +e.target.value);
$("run").onclick = run;
$("adv").onchange = e => document.body.classList.toggle("showadv",
                                                       e.target.checked);
$("lang").onchange = async e => {
  LANG = e.target.value;
  history.replaceState(null, "", `?l=${LANG}`);
  await loadSpec(); await loadExamples(); chrome(); drawGrid();
};

(async () => {
  await loadSpec();
  await loadExamples();
  chrome();
  // ONE EMPTY ROW, and nothing runs. The first version seeded three rows and
  // ran them on load, which also fired a model call on every page open — a
  // request to a provider per visitor, unasked. The way in is the examples
  // drop-down or the question box; the table starts as a table.
  addRow();
  $("report").innerHTML = `<p class="muted">${esc(t("nothing"))}</p>`;
})();
