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
        thinking: "filling the table…", pick: "— pick —",
        aioff: "no model key — the table and the verdict work without it" },
  ru: { advanced: "дополнительно", reference: "что такое ZFL? (язык)",
        addrow: "добавить строку", run: "запустить", claim: "утверждение",
        remove: "убрать строку",
        nothing: "пока нечего показывать — заполните строку и запустите",
        applies: "приборы, которым было что сказать",
        passport: "паспорта", numeric: "числовой пол",
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
        thinking: "заполняю таблицу…", pick: "— выберите —",
        aioff: "ключа модели нет — таблица и вердикт работают и без неё" },
};

let LANG = new URLSearchParams(location.search).get("l") === "ru" ? "ru" : "en";
let SPEC = null;
let ROWS = [];

const $ = id => document.getElementById(id);
const t = k => UI[LANG][k] || k;

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
    out.push(panel(t("judge"),
      `<p>${t("verdict")}: ${verdictSpan(rep.judge.verdict)} · ` +
      `${t("grade")}: ${esc(rep.judge.grade)}</p>` +
      (rep.judge.unverified.length
        ? `<p class="muted">${t("weak")}: ` +
          esc(rep.judge.unverified.join(", ")) + "</p>" : "")));
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
    body: JSON.stringify({ history: HISTORY, lang: LANG }),
  }).then(x => x.json());
  pending.remove();
  if (!r.ok) { addMsg("sys", r.error || (r.issues || []).map(i => i.hint)
                             .join("; ")); return; }
  ROWS = r.doc.rows || [];
  $("claim").value = r.doc.claim || "";
  HISTORY.push({ role: "assistant", content: JSON.stringify(r.doc) });
  drawGrid();
  run();
}

async function commentary(doc, result) {
  const r = await fetch("/api/v2comment", {
    method: "POST", headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ doc, result, lang: LANG }),
  }).then(x => x.json());
  if (!r.ok) return;
  const d = document.createElement("div");
  d.className = "panel comment";
  d.innerHTML = `<h3>${esc(t("commentary"))}</h3><p>${esc(r.reply)}</p>`;
  $("report").appendChild(d);
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
  $("lang").textContent = LANG === "en" ? "RU" : "EN";
  $("ref").href = `/zfl?l=${LANG}`;
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
$("addrow").onclick = addRow;
$("send").onclick = ask;
$("ask").onkeydown = e => { if (e.key === "Enter") ask(); };
$("exkind").onchange = e => fillItems(e.target.value);
$("exitem").onchange = e => loadExample($("exkind").value, +e.target.value);
$("run").onclick = run;
$("adv").onchange = e => document.body.classList.toggle("showadv",
                                                       e.target.checked);
$("lang").onclick = async () => {
  LANG = LANG === "en" ? "ru" : "en";
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
