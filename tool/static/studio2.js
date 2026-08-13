// ZTL Studio v2 — the table, built from the spec the validator enforces.
//
// This file knows no column names, no statuses, no options and no labels.
// It asks /api/formspec and draws what it is told, so the language lives in
// one place (tool/zfl2.py) and the front-end cannot drift from it. The only
// thing hard-coded here is the handful of words belonging to the CHROME —
// buttons and headings that are not part of the language.

const UI = {
  en: { advanced: "advanced", reference: "what is ZFL?", addrow: "add a row",
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
        prov: "provenance", still: "still a box" },
  ru: { advanced: "дополнительно", reference: "что такое ZFL?",
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
        prov: "происхождение", still: "ещё коробка" },
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
function widget(col, row, i) {
  const v = row[col.key] ?? col.default ?? "";
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
  const hint = (col.eg || [])[0];
  return `<input type="text" data-i="${i}" data-k="${esc(col.key)}" ` +
         `value="${esc(v)}" placeholder="${hint ? esc(t("eg") + hint) : ""}">`;
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
  return { rows: ROWS.filter(r => (r.name || "").trim()),
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
    out.push(panel(t("numeric"),
      `<p>${verdictSpan(rep.numeric.disposition)}</p>` + solvedTable +
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

// ------------------------------------------------------------------ wiring
async function run() {
  const r = await fetch("/api/v2run", {
    method: "POST", headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ doc: collect() }),
  }).then(x => x.json());
  showIssues(r.issues);
  if (r.ok) showReport(r); else $("report").innerHTML = "";
}

function chrome() {
  document.querySelectorAll("[data-t]").forEach(e =>
    e.textContent = t(e.dataset.t));
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
});
document.addEventListener("click", e => {
  const d = e.target.dataset?.del;
  if (d != null) { ROWS.splice(+d, 1); drawGrid(); }
});
$("addrow").onclick = addRow;
$("run").onclick = run;
$("adv").onchange = e => document.body.classList.toggle("showadv",
                                                       e.target.checked);
$("lang").onclick = async () => {
  LANG = LANG === "en" ? "ru" : "en";
  history.replaceState(null, "", `?l=${LANG}`);
  await loadSpec(); chrome(); drawGrid();
};

(async () => {
  await loadSpec();
  chrome();
  // one row of each kind, so the first screen shows what the table is FOR
  // rather than an empty grid: an invoice line, its ceiling, and the liar.
  ROWS = [
    { name: "line", means: "the invoice line", status: "verified",
      ground: "inv-17", ground_kind: "document", value: "1500", unit: "RUB" },
    { name: "budget", means: "the ceiling", status: "verified",
      ground: "order-4", ground_kind: "document", value: "5000", unit: "RUB" },
    { name: "L", means: "this sentence is false", status: "defined",
      ground: "~Tr(L)", ground_kind: "document" },
  ];
  drawGrid();
  $("claim").value = "line <= budget";
  run();
})();
