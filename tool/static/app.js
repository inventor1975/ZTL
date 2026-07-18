"use strict";

const $ = id => document.getElementById(id);
const chatBox = $("chat"), zflBox = $("zfl");
let history = [];
let lastRun = null;          // {zfl, back_reading, report}
let explainHistory = [];
let cfg = JSON.parse(localStorage.getItem("ztl_cfg") || "{}");  // {provider, model, key}

const AI = new Set(["/api/chat", "/api/emit", "/api/repair",
                    "/api/explain"]);
async function api(path, payload) {
  if (AI.has(path) && payload) payload = {...payload, cfg};
  try {
    const r = await fetch(path, payload === undefined ? {} : {
      method: "POST", headers: {"Content-Type": "application/json"},
      body: JSON.stringify(payload)});
    return await r.json();
  } catch (e) {
    return {ok: false, error: "connection to the studio lost: " + e,
            issues: [{level: "error", code: "E_NET", where: path,
                      hint: String(e)}]};
  }
}

function mdLite(text) {
  let s = String(text).replace(/&/g, "&amp;").replace(/</g, "&lt;");
  s = s.replace(/\*\*([^*\n]+)\*\*/g, "<b>$1</b>");
  s = s.split("\n").map(line => {
    if (/^#{1,3}\s+/.test(line))
      return "<b>" + line.replace(/^#{1,3}\s+/, "") + "</b>";
    if (/^[-*]\s+/.test(line))
      return "• " + line.replace(/^[-*]\s+/, "");
    if (/^---+$/.test(line)) return "";
    return line;
  }).join("\n");
  return s;
}

function addMsg(role, text) {
  const d = document.createElement("div");
  d.className = "msg " + role;
  d.innerHTML = mdLite(text);
  chatBox.appendChild(d);
  chatBox.scrollTop = chatBox.scrollHeight;
  return d;
}

/* ---------------------------------------------------------- 1. chat */
$("btn-send").onclick = async () => {
  const text = $("chat-input").value.trim();
  if (!text) return;
  $("chat-input").value = "";
  addMsg("user", text);
  history.push({role: "user", content: text});
  addMsg("ai", "…");
  const r = await api("/api/chat", {history, mode});
  chatBox.lastChild.remove();
  if (!r.ok) { addMsg("err", r.error); return; }
  addMsg("ai", r.reply);
  history.push({role: "assistant", content: r.reply});
};
$("chat-input").addEventListener("keydown", e => {
  if (e.key === "Enter" && !e.shiftKey) { e.preventDefault(); $("btn-send").click(); }
});

$("btn-agree").onclick = async () => {
  const last = [...history].reverse().find(m => m.role === "assistant");
  if (!last) { addMsg("err", "get an understanding from the AI first"); return; }
  addMsg("ai", "compiling to ZFL…");
  const r = await api("/api/emit", {understanding: last.content, mode});
  chatBox.lastChild.remove();
  if (!r.ok) { addMsg("err", r.error); return; }
  zflBox.value = pretty(r.zfl);
  addMsg("ai", "ZFL is ready — panel 2. Check the back-reading and run.");
  validate();
};

function pretty(s) {
  try { return JSON.stringify(JSON.parse(s), null, 1); } catch { return s; }
}

/* ----------------------------------------------------------- 2. ZFL */
function showIssues(issues) {
  $("issues").innerHTML = "";
  for (const i of issues || []) {
    const d = document.createElement("div");
    d.className = "issue " + i.level;
    d.textContent = `${i.code} @ ${i.where}: ${i.hint}`;
    $("issues").appendChild(d);
  }
}

async function validate() {
  const r = await api("/api/validate", {zfl: zflBox.value});
  showIssues(r.issues);
  $("vstatus").textContent = r.ok ? "✓ valid" : "✗ errors";
  $("vstatus").style.color = r.ok ? "var(--ok)" : "var(--bad)";
  const br = $("backread");
  if (r.back_reading) { br.textContent = r.back_reading; br.classList.remove("hidden"); }
  else br.classList.add("hidden");
  return r.ok;
}
$("btn-validate").onclick = validate;

$("btn-repair").onclick = async () => {
  $("vstatus").textContent = "repairing…";
  $("vstatus").style.color = "var(--dim)";
  const r = await api("/api/repair", {zfl: zflBox.value});
  if (!r.ok) {
    showIssues(r.issues);
    $("vstatus").textContent = r.error || "✗ repair failed";
    $("vstatus").style.color = "var(--bad)";
    return;
  }
  zflBox.value = pretty(r.zfl);
  validate();
};

/* ------------------------------------------------------- 3. results */
$("btn-run").onclick = async () => {
  const path = mode === "hyp" ? "/api/refute"
             : mode === "ast" ? "/api/assert" : "/api/run";
  const r = await api(path, {zfl: zflBox.value});
  showIssues(r.issues);
  const out = $("report");
  out.innerHTML = "";
  if (!r.ok) { $("vstatus").textContent = "✗ fix the errors first"; $("vstatus").style.color = "var(--bad)"; return; }
  if (r.back_reading) { $("backread").textContent = r.back_reading; $("backread").classList.remove("hidden"); }
  let rep;
  if (mode === "hyp") { rep = r.result; renderRefute(rep, out); }
  else if (mode === "ast") {
    rep = r.report;
    renderLogicMap(rep.logic_map, out);
    renderStatement(rep, out);
  }
  else { rep = r.report; if (rep.genre === "statement") renderStatement(rep, out); else renderSystem(rep, out); }
  const lastUser = [...history].reverse().find(m => m.role === "user");
  lastRun = {zfl: zflBox.value, back_reading: r.back_reading || "",
             report: rep, lang_hint: lastUser ? lastUser.content : ""};
  explainHistory = [];
  $("explain-chat").innerHTML = "";
  $("explain-wrap").classList.remove("hidden");
  await explainStep();       // the first, unprompted explanation
};

function addExp(role, text) {
  const d = document.createElement("div");
  d.className = "msg " + (role === "user" ? "user" : "exp");
  d.innerHTML = role === "user" ? mdLite(text).replace(/<b>|<\/b>/g, "")
                                : mdLite(text);
  $("explain-chat").appendChild(d);
  $("explain-chat").scrollTop = $("explain-chat").scrollHeight;
  return d;
}

async function explainStep() {
  const wait = addExp("exp", "…");
  const r = await api("/api/explain", {...lastRun, history: explainHistory});
  wait.remove();
  if (!r.ok) { addExp("exp", r.error); return; }
  addExp("exp", r.reply);
  explainHistory.push({role: "assistant", content: r.reply});
}

$("btn-explain").onclick = async () => {
  const q = $("explain-input").value.trim();
  if (!q || !lastRun) return;
  $("explain-input").value = "";
  addExp("user", q);
  explainHistory.push({role: "user", content: q});
  await explainStep();
};
$("explain-input").addEventListener("keydown", e => {
  if (e.key === "Enter" && !e.shiftKey) { e.preventDefault(); $("btn-explain").click(); }
});

function el(tag, html) { const d = document.createElement(tag); d.innerHTML = html; return d; }
function esc(s) { return String(s).replace(/&/g,"&amp;").replace(/</g,"&lt;"); }

function renderStatement(rep, out) {
  out.appendChild(el("div",
    `<div class="verdict">verdict: <span class="${rep.verdict}">${rep.verdict}</span>
     <small>· warranty: ${esc(rep.warranty)}</small></div>`));
  out.appendChild(el("p", esc(rep.verdict_class)));
  out.appendChild(el("p", `passport: ${esc(rep.passport)}`));
  if (rep.completions.length) {
    let rows = rep.completions.map(c =>
      `<tr><td>${esc(c.case)}</td><td class="verdict"><span class="${c.value}">${c.value}</span></td></tr>`).join("");
    out.appendChild(el("table",
      `<tr><th>completion of the unverified</th><th>value</th></tr>${rows}`));
  }
}

function renderSystem(rep, out) {
  out.appendChild(el("p", `<b>${esc(rep.summary)}</b>`));
  const g = Object.entries(rep.grounded);
  if (g.length) {
    out.appendChild(el("div", "grounded: " + g.map(([k, v]) =>
      `<span class="pill">${esc(k)} = <b class="${v}">${v}</b></span>`).join("")));
  }
  let rows = rep.passports.map(p =>
    `<tr><td>${esc(p.component.join(", "))}</td>
     <td class="kind-${p.kind}">${esc(p.kind_txt)}</td>
     <td>${esc(p.detail)}</td></tr>`).join("");
  if (rows) out.appendChild(el("table",
    `<tr><th>component</th><th>passport</th><th>details</th></tr>${rows}`));
  for (const s of rep.stipulations) {
    out.appendChild(el("p",
      `stipulations for {${esc(s.component.join(", "))}}: ` +
      s.models.map(m => `<span class="pill">${esc(m)}</span>`).join(" or ")));
  }
}

/* -------------------------------------------- examples (mode-aware) */
let PARADOX_EX = [];
const HYP_EX = [
  {name: "p → p  (reflexivity of the arrow)", intent: "Does p imply p — is the arrow reflexive?",
   zfl: 'assert p impl p'},
  {name: "¬p → ¬p", intent: "Does not-p imply not-p?",
   zfl: 'assert !p impl !p'},
  {name: "excluded middle:  p ∨ ¬p", intent: "Is 'p or not p' always true?",
   zfl: 'assert p or !p'},
  {name: "¬¬p ∨ ¬p  (LEM is not all bad)", intent: "Is '¬¬p or ¬p' always true?",
   zfl: 'assert !!p or !p'},
  {name: "¬¬¬p ↔ ¬p  (triple = single ¬)", intent: "Does ¬¬¬p equal ¬p?",
   zfl: 'assert !!!p iff !p'},
  {name: "¬¬p  (double negation alone)", intent: "Is ¬¬p always true?",
   zfl: 'assert !!p'},
  {name: "∧-elimination:  (a∧b) → a", intent: "Does 'a and b' imply a?",
   zfl: 'assert (a and b) impl a'},
  {name: "∨-introduction:  a → (a∨b)", intent: "Does a imply 'a or b'?",
   zfl: 'assert a impl (a or b)'},
];
const AST_EX = [
  {name: "syllogism: from p→q, q→r and p, r follows",
   intent: "If p implies q, q implies r, and p holds — then r holds.",
   zfl: 'assert ((p impl q) and ((q impl r) and p)) impl r'},
  {name: "¬¬p → p  (double negation elimination)",
   intent: "If it is false that p is false, then p is true.",
   zfl: 'assert !!p impl p'},
  {name: "identity of denials: ¬p → ¬p",
   intent: "A denial follows from itself.",
   zfl: 'assert !p impl !p'},
  {name: "“not disproved — hence guilty”",
   intent: "If the accusation is not disproved, the person is guilty.",
   zfl: 'assert !refuted impl guilty'},
  {name: "p → p  (identity)",
   intent: "Every assertion follows from itself.",
   zfl: 'assert p impl p'},
];

function fillExamples(list) {
  const sel = $("examples");
  sel.innerHTML = '<option value="">— examples —</option>';
  list.forEach((e, i) => {
    const o = document.createElement("option");
    o.value = String(i); o.textContent = e.name; sel.appendChild(o);
  });
  sel.onchange = () => {
    const e = list[+sel.value];
    if (!e) return;
    if (e.intent) $("chat-input").value = e.intent;   // ready for “Understand”
    if (e.zfl) {                          // human line as-is; JSON pretty-printed
      zflBox.value = e.zfl.trim().startsWith("{") ? pretty(e.zfl) : e.zfl;
      validate();
    }
  };
}

(async () => { PARADOX_EX = await api("/api/examples"); applyMode(); })();


/* -------------------------------------------------------- settings */
let providersList = [];
async function loadProviders() {
  const r = await api("/api/providers", {});
  providersList = r.providers || [];
  if (r.public) {                       // public instance: keys are session-only
    const sv = $("set-save");
    if (sv) sv.style.display = "none";
  }
  const sel = $("set-provider");
  sel.innerHTML = "";
  for (const p of providersList) {
    const o = document.createElement("option");
    o.value = p.provider;
    o.textContent = p.label + (p.has_key ? " ✓" : " (no key)");
    sel.appendChild(o);
  }
  if (cfg.provider) sel.value = cfg.provider;
  syncSettings();
}
function currentProv() {
  return providersList.find(p => p.provider === $("set-provider").value);
}
function syncSettings() {
  const p = currentProv();
  const link = $("set-console");
  if (p && p.console) {
    link.href = p.console;
    link.textContent = p.label.replace(/\s*\(.*\)/, "") + " console ↗";
    link.style.display = "";
  } else { link.style.display = "none"; }
  const msel = $("set-model");
  msel.innerHTML = "";
  const models = (p && p.models && p.models.length) ? p.models
                 : (p ? [p.default_model] : []);
  for (const m of models) {
    const o = document.createElement("option");
    o.value = m; o.textContent = m; msel.appendChild(o);
  }
  const want = (cfg.provider === $("set-provider").value && cfg.model)
               ? cfg.model : (p ? p.default_model : "");
  if (want && models.includes(want)) msel.value = want;
  $("set-status").textContent = p
    ? (p.has_key ? "✓ a key is stored for this provider"
                 : "no stored key — paste one or set the env var")
    : "";
  $("set-status").className = p && p.has_key ? "has-key" : "no-key";
}
$("btn-settings").onclick = () => { $("settings").classList.remove("hidden"); loadProviders(); };
$("set-x").onclick = () => $("settings").classList.add("hidden");
$("settings").addEventListener("click", e => {
  if (e.target === $("settings")) $("settings").classList.add("hidden");
});
document.addEventListener("keydown", e => {
  if (e.key === "Escape") $("settings").classList.add("hidden");
});
$("set-provider").onchange = syncSettings;
$("set-close").onclick = () => {
  cfg = {provider: $("set-provider").value,
         model: $("set-model").value.trim(),
         key: $("set-key").value.trim() || cfg.key || ""};
  localStorage.setItem("ztl_cfg", JSON.stringify(cfg));
  $("settings").classList.add("hidden");
  updateAiWarn();                        // reflect the newly chosen provider
};
$("set-save").onclick = async () => {
  const key = $("set-key").value.trim();
  if (!key) { $("set-status").textContent = "paste a key first"; return; }
  const r = await api("/api/savekey",
    {provider: $("set-provider").value, key});
  $("set-status").textContent = r.ok ? "✓ saved to tool/." +
    $("set-provider").value + "_key" : ("✗ " + r.error);
  $("set-key").value = "";
  cfg = {provider: $("set-provider").value,
         model: $("set-model").value.trim(), key: ""};
  localStorage.setItem("ztl_cfg", JSON.stringify(cfg));
  loadProviders();
};

/* --------------------------------------- mode: Hypotheses / Paradoxes */
let mode = "hyp";                       // Hypotheses is the first/default tab
const tabState = {par: null, hyp: null, ast: null};   // independent per-tab state

function applyMode() {
  const hyp = mode === "hyp", ast = mode === "ast";
  $("p1-title").innerHTML = ast
    ? '1 · Assertion <small>state an assertion — the AI formalizes, the core maps its logic</small>'
    : hyp
    ? '1 · Hypothesis <small>a claimed law / rule — describe it, the AI formalizes, the core checks it</small>'
    : '1 · Meta-chat <small>negotiating the meaning; the AI only translates, never judges</small>';
  $("chat-input").placeholder = ast
    ? "State an assertion — any language (e.g. “not disproved, hence guilty”)…"
    : hyp
    ? "Describe a law or rule to check — any language (e.g. “does p imply p?”)…"
    : "Describe a claim, a paradox, a situation — any language…";
  $("btn-run").textContent = ast ? "Map the logic"
    : hyp ? "Check hypothesis on the core" : "Run on the core";
  fillExamples(ast ? AST_EX : hyp ? HYP_EX : PARADOX_EX);
}

/* each tab keeps its OWN chat, ZFL and output — snapshot on leave, restore on enter */
function snapshot() {
  return {
    chat: chatBox.innerHTML, history: history.slice(),
    zfl: zflBox.value,
    issues: $("issues").innerHTML, report: $("report").innerHTML,
    backread: $("backread").innerHTML,
    backreadHidden: $("backread").classList.contains("hidden"),
    explain: $("explain-chat").innerHTML,
    explainWrapHidden: $("explain-wrap").classList.contains("hidden"),
    vstatus: $("vstatus").textContent, vstatusColor: $("vstatus").style.color,
    lastRun, explainHistory: explainHistory.slice(),
  };
}
function restore(s) {
  if (!s) {                              // fresh tab — clear everything
    chatBox.innerHTML = ""; history = []; zflBox.value = "";
    $("issues").innerHTML = ""; $("report").innerHTML = "";
    $("backread").innerHTML = ""; $("backread").classList.add("hidden");
    $("explain-chat").innerHTML = ""; $("explain-wrap").classList.add("hidden");
    $("vstatus").textContent = ""; lastRun = null; explainHistory = [];
    return;
  }
  chatBox.innerHTML = s.chat; history = s.history;
  zflBox.value = s.zfl;
  $("issues").innerHTML = s.issues; $("report").innerHTML = s.report;
  $("backread").innerHTML = s.backread;
  $("backread").classList.toggle("hidden", s.backreadHidden);
  $("explain-chat").innerHTML = s.explain;
  $("explain-wrap").classList.toggle("hidden", s.explainWrapHidden);
  $("vstatus").textContent = s.vstatus; $("vstatus").style.color = s.vstatusColor;
  lastRun = s.lastRun; explainHistory = s.explainHistory;
}

document.querySelectorAll(".tab").forEach(t => t.onclick = () => {
  const newMode = t.dataset.tab;
  if (newMode === mode) return;
  tabState[mode] = snapshot();           // save the leaving tab
  document.querySelectorAll(".tab").forEach(x => x.classList.remove("active"));
  t.classList.add("active");
  mode = newMode;
  setTabTint(mode);
  restore(tabState[mode]);               // load the entering tab (null = fresh)
  applyMode();
});

// background tint per tab, on body (whole page) and main (content area) so
// the switch is unmistakable
function setTabTint(m) {
  document.body.classList.toggle("tab-par", m === "par");
  document.body.classList.toggle("tab-hyp", m === "hyp");
  document.body.classList.toggle("tab-ast", m === "ast");
}

// the free-model warning: show when the active provider is Groq
function updateAiWarn() {
  const prov = (cfg && cfg.provider) ||
               (providersList[0] && providersList[0].provider) || "groq";
  const w = $("ai-warn");
  if (w) w.classList.toggle("hidden", prov !== "groq");
}

setTabTint("hyp");   // default tab background
applyMode();   // render the default (Hypotheses) view immediately
loadProviders().then(updateAiWarn);       // populate providers, hide save, set warning

/* the refuter verdict (Hypotheses mode) rendered into #report */
function renderRefute(res, out) {
  const cefmt = ce => Object.entries(ce).map(([a, v]) => `${a}=${v}`).join(", ");
  let head, body;
  if (res.outcome === "CONFIRMED") {
    head = "✅ CONFIRMED";
    body = "Holds under every assignment — including any unverified (Z) inputs.";
  } else if (res.outcome === "REFUTED_CLASSICAL") {
    head = "❌ REFUTED (classically)";
    body = "Fails already on verified inputs — a plain logic error.<br>" +
           "counterexample: <code>" + cefmt(res.counterexample) + "</code>";
  } else {
    head = "⚠️ REFUTED (under uncertainty)";
    const zs = Object.entries(res.counterexample).filter(([, v]) => v === "Z")
      .map(([a]) => a).join(", ");
    body = "Holds when every input is verified, but BREAKS when an input is " +
           "unverified — silent trust laundering.<br>killing marking: <code>" +
           cefmt(res.counterexample) + "</code>  (unverified: " + zs + ")";
  }
  const atoms = (res.atoms || []).join(", ") || "(none)";
  out.appendChild(el("div",
    `<div class="card refute-result"><h3>${head}</h3>` +
    `<p class="dim">atoms: ${atoms}</p><p>${body}</p></div>`));
}

/* ---------------------------------------- Assertion: the logic map */
function renderLogicMap(map, out) {
  if (!map) return;
  const esc2 = s => String(s).replace(/</g, "&lt;");
  const wfmt = w => Object.entries(w || {}).map(([a, v]) => `${a}=${v}`).join(", ");
  let cur = map.currency, head, cls;
  if (cur.kind === "free-truth") { head = "🟢 FREE TRUTH — a guarded ZTL tautology"; cls = "ok"; }
  else if (cur.kind === "on-credit") { head = "🟡 ON CREDIT — classically valid, breaks on unverified input"; cls = "warn"; }
  else { head = "⚪ CONTINGENT — depends on the facts"; cls = "dim"; }
  let html = `<div class="card"><h3>Logic map</h3>`
    + `<p><code>${esc2(map.formula)}</code></p>`
    + `<p><b>${head}</b><br><span class="dim">${esc2(cur.note)}</span>`
    + (cur.witness && Object.keys(cur.witness).length
       ? `<br>witness: <code>${esc2(wfmt(cur.witness))}</code>` : "")
    + `</p>`;
  if (map.decisive && map.decisive.length) {
    html += `<p><b>Decisive checks</b><br>` +
      map.decisive.map(d =>
        `<code>${esc2(d.atom)}</code>: verify T → ${d.T}, verify F → ${d.F}`)
      .join("<br>") + `</p>`;
  }
  const a = map.audit;
  if (a) {
    const label = {earned: "✅ EARNED — alive rules only",
                   "on-credit": "🟡 ON CREDIT — a fallen rule is borrowed",
                   "rules-gap": "🕳 RULES GAP — forced semantically, unreachable by the battery",
                   "does-not-follow": "❌ DOES NOT FOLLOW",
                   skipped: "— audit skipped"}[a.status] || a.status;
    html += `<p><b>Derivation audit: ${label}</b>`
      + (a.loans ? `<br>loan: <code>${a.loans.join(", ")}</code>` : "")
      + (a.counterexample
         ? `<br>counterexample: <code>${esc2(wfmt(a.counterexample))}</code>` : "")
      + `<br><span class="dim">${esc2(a.note)}</span></p>`;
    if (a.chain) {
      html += `<pre class="dim" style="white-space:pre-wrap">`
        + a.chain.map(esc2).join("\n") + `</pre>`;
    }
  }
  html += `</div>`;
  out.appendChild(el("div", html));
}
