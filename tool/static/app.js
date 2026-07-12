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
  const r = await api("/api/chat", {history});
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
  const r = await api("/api/emit", {understanding: last.content});
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
  const r = await api("/api/run", {zfl: zflBox.value});
  showIssues(r.issues);
  const out = $("report");
  out.innerHTML = "";
  if (!r.ok) { $("vstatus").textContent = "✗ fix the errors first"; $("vstatus").style.color = "var(--bad)"; return; }
  if (r.back_reading) { $("backread").textContent = r.back_reading; $("backread").classList.remove("hidden"); }
  const rep = r.report;
  if (rep.genre === "statement") renderStatement(rep, out);
  else renderSystem(rep, out);
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

/* -------------------------------------------------------- examples */
(async () => {
  const ex = await api("/api/examples");
  for (const e of ex) {
    const o = document.createElement("option");
    o.value = e.name; o.textContent = e.name;
    $("examples").appendChild(o);
  }
  $("examples").onchange = () => {
    const e = ex.find(x => x.name === $("examples").value);
    if (!e) return;
    addMsg("user", e.intent);
    zflBox.value = e.zfl;
    validate();
  };
})();


/* -------------------------------------------------------- settings */
let providersList = [];
async function loadProviders() {
  const r = await api("/api/providers", {});
  providersList = r.providers || [];
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
  $("set-model").placeholder = p ? p.default_model : "default";
  $("set-model").value = (cfg.provider === $("set-provider").value)
    ? (cfg.model || "") : "";
  $("set-status").textContent = p
    ? (p.has_key ? "✓ a key is stored for this provider"
                 : "no stored key — paste one or set the env var")
    : "";
  $("set-status").className = p && p.has_key ? "has-key" : "no-key";
}
$("btn-settings").onclick = () => { $("settings").classList.remove("hidden"); loadProviders(); };
$("set-provider").onchange = syncSettings;
$("set-close").onclick = () => {
  cfg = {provider: $("set-provider").value,
         model: $("set-model").value.trim(),
         key: $("set-key").value.trim() || cfg.key || ""};
  localStorage.setItem("ztl_cfg", JSON.stringify(cfg));
  $("settings").classList.add("hidden");
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
