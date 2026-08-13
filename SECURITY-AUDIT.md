# Security audit — the judge and ZTLStudio

*2026-08-13, before the studio upgrade. Method: read the code, then MEASURE
the suspicions rather than report them. Every number below was produced on
this machine and can be reproduced from the commands quoted.*

Scope: everything a request from the public internet can reach —
`tool/ztlstudio.py` (the HTTP layer), `tool/zfl.py` and `tool/engine.py`
(the parsers and the runner), and the core the routes call into
(`ztljudge`, `znumjudge`, `znumsolve`, `zpassport`). The public instance is
`ztl.vitalyreznik.com`, served behind an Apache reverse proxy.

---

## Clean — checked, with the evidence

**Code injection: structurally impossible.** There is no `eval`, no `exec`,
no `pickle`, no `os.system`, no `__import__` anywhere in the core or the
studio. The formula parsers are hand-written over regular expressions. This
is the finding that matters most in a service whose entire job is to accept
formulas from strangers, and it holds by construction rather than by
vigilance.

**XSS: no live vector.** All text from the server reaches the DOM through
`textContent` or through `esc()`. `mdLite`, which does build HTML from
model output, escapes `&` and `<` on its first line, before any markup is
introduced — the order is right, and it was the first thing suspected here.

**Path traversal: closed twice.** `/static/` reduces the request to
`os.path.basename`, so nothing outside `tool/static/` can be read. The only
endpoint that WRITES, `/api/savekey`, takes its filename from a fixed
provider table and never from the request, chmods to 600, and is disabled
outright on the public instance.

**Exponential blowup: real in the library, capped at the surface.** The
passport office enumerates classical solutions, and the cost is exactly what
the docket says it is — measured on cycles: 18 sentences 0.36 s, 20 sentences
1.46 s, 22 sentences 6.45 s, 24 sentences 26.88 s. Doubling per sentence, so
30 sentences would be about half an hour of a worker. It is not reachable:
`zfl.validate` refuses more than ten names with `E_TOOBIG` and states the
reason in the message ("cost is 3**names"), and every core route —
`/api/run`, `/api/validate`, `/api/assert`, and `/api/refute` through
`refuter` — passes through that cap. A 256 KB body limit sits in front of it,
with the proxied body correctly drained before the 413 so Apache does not see
a desync.

**Hostile parser input: rejected or contained.** A hundred-thousand-digit
integer and `1e100000` are both refused with `ValueError`; a witness field
stuffed with twenty thousand commas likewise; four hundred nested
parentheses parse normally; five thousand conjoined atoms raise
`RecursionError`, which the handler catches. Nothing hung, nothing crashed
the process.

---

## Findings

### 1. A provider call blocks the whole studio — MEDIUM (availability)

The server is `HTTPServer`, which serves one request at a time, and the AI
routes call `urllib.request.urlopen(req, timeout=90)` inside the handler. So
a single slow completion freezes the public studio for every visitor for up
to a minute and a half. The free-AI rate limit (20 per 10 minutes per IP)
bounds abuse from one address and does nothing about a slow provider or a
handful of addresses.

*Fix:* `ThreadingHTTPServer`. NOT applied here, and deliberately: it
introduces concurrency into code with module-level mutable state (`_RL`, the
translator's caches), so it wants a read of that state and a test, not a
one-word substitution on a live service. That is the curator's call.

### 2. The exception message is returned to the client — LOW (disclosure)

The catch-all in `do_POST` answers with `f"internal studio error: {e}"`. An
exception's text can carry absolute paths, module internals or fragments of
input. It should say something generic and log the detail server-side.

*Applied.* The client now gets the exception TYPE and nothing else.

### 3. `esc()` does not escape quotes — LATENT (would become XSS)

`esc()` replaces `&` and `<` only, which is sufficient for text nodes and
insufficient for attributes. Four places interpolate values into `class="…"`
without escaping at all (`rep.verdict`, `c.value`, `p.kind`, and a grounded
value). Those come from the core's closed vocabulary today — `T`, `F`, `Z`,
`PARADOX` and so on — so there is no live vector. It is a trap for the next
edit: the day a sentence NAME lands in an attribute, it is an injection.

*Applied.* `esc()` now escapes `"` and `'` as well, and the four attribute
interpolations go through it. Costs nothing and removes the trap.

### 4. No access log — LOW (operational)

`log_message` is overridden to discard everything. On a public instance that
removes the ability to investigate abuse after the fact, or to notice it at
all. Not a vulnerability; a missing instrument.

### 5. `http.server` in production — accepted, worth stating

The standard library documents it as not for production use. Behind Apache
the exposure is much reduced. Recorded so that the choice is a choice.

---

## Ceiling — what this audit did not cover

The Apache configuration and TLS termination; the provider keys' handling
beyond the save endpoint; the LLM's own outputs as a vector for socially
engineered self-XSS (the escaping holds, but a user can still be talked into
pasting something); dependency supply chain; and anything about the host.
This audit read the application and measured it, and that is all it claims.
