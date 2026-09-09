# bench — code2zfl against labelled corpora (2026-09-09)

The fixtures in `../fixtures` test the questions I thought of. A labelled corpus written by
someone else tests the ones I did not. Two were used, both public, neither committed here:

    git clone --depth 1 https://github.com/stivalet/PHP-Vulnerability-test-suite.git   # SARD / Stivalet, 42 212 files
    git clone --depth 1 https://github.com/digininja/DVWA.git                          # DVWA, four levels per flaw

`sard.py` runs code2zfl over one CWE directory and scores the file verdict (worst sink of the
context) against the directory label. `psalm_sard.py` runs Psalm 5 `--taint-analysis` over the
same directory and joins the three: label, Psalm, ours. Whole suite: ~10 s for us, ~15 s for Psalm.

## What the corpus is, and what it is not

Sources in the suite: `$_GET`, `$_POST`, `$_GET` through an array — these are in the base catalog.
`$_SESSION`, the output of `fopen`/`exec`/`system`/`popen`/`proc_open`/backticks/`unserialize`, and
four in-file getter objects (`$temp->getInput()`) are **Z by policy** (curator, 2026-09-08: DB and
session stay Z; an unknown call is not visible) — they come back OPEN, never EARNED and never
REFUTED. So 3 of 16 sources are measured against the label; 13 are measured against *silence*: an
OPEN there is right, an EARNED would be a lie. Every unsafe→EARNED count below is checked against
that: none comes from those 13 sources.

## Measured (base catalog, no overlay) — before and after this pass

The two numbers that matter: **unsafe→EARNED** (the instrument says "clean" on a planted flaw)
and **safe→REFUTED** (an alarm on a fixed one). "before" = the tool as of commit b451690.

| CWE / ctx | unsafe n | R / O / E before | R / O / E after | **miss** before→after | safe n | R / O / E before | R / O / E after | **false alarm** before→after |
|---|---:|---|---|---|---:|---|---|---|
| 89 sql | 912 | 153 / 555 / 204 | 153 / 759 / **0** | 204 → **0** | 8640 | 1053 / 4095 / 3492 | **90** / 1062 / 7488 | 1053 → **90** |
| 78 shell | 624 | 99 / 393 / 132 | 96 / 512 / 16 | 132 → 16 | 1872 | 264 / 888 / 720 | 114 / 558 / 1200 | 264 → 114 |
| 98 file | 672 | 108 / 420 / 0 | 102 / 538 / 32 | 0 → 32 | 2592 | 330 / 1182 / 348 | 102 / 570 / 1740 | 330 → 102 |
| 601 header | 2592 | 225 / 771 / 300 | 384 / 1856 / 352 | 300 → 352 | 2208 | 120 / 456 / 528 | **0** / 128 / 2080 | 120 → **0** |
| 79 html | 4352 | 540 / 2196 / 1616 | 372 / 2188 / 1792 | 1616 → 1792 | 5728 | 480 / 1824 / 3424 | 168 / 1112 / 4448 | 480 → 168 |
| 95 code | 336 | 54 / 210 / 72 | 51 / 281 / 4 | 72 → 4 | 1296 | 159 / 801 / 336 | 45 / 831 / 420 | 159 → 45 |

(CWE_98/601 "before" also had 876 / 2400 files with no sink found: a constant `include`, and
`http_redirect()` which was not in the catalog.)

### Every remaining unsafe→EARNED, read in the source

* **`sprintf('%d')` constructions** (78: 16, 98: 32, 601: 32+32, 95: 4). The suite's generator
  labels a file by its sanitizer token; `include(sprintf("pages/'%d'.php", $tainted))` formats a
  number whatever came in. Our EARNED is right; the label is the generator's defect.
* **Letters-only guard before `header("Location: " . $x)`** (601: 288). `^[a-zA-Z0-9]*$` cannot
  spell a host or a scheme; the suite marks every non-whitelist URL unsafe. Ours stands.
* **HTML sub-contexts** (79: 1792) — **a real boundary, not a label defect.** `htmlspecialchars`,
  a numeric filter or a whitelist is credited by us as an `html` substitution; the suite puts the
  value into an unquoted attribute (`<div id=$x>`), a tag name (`<$x href=…>`), an event handler,
  `<script>`, `<style>`. There a space, a letter or a digit string is enough. Our `html` context has
  no sub-contexts yet (the way `sql` has quoted/unquoted). Named here; not built.

### Every remaining safe→REFUTED

* **Declared disagreements** (the same 5 tokens in every CWE, 18 each on the 3 measured sources):
  `addslashes`, `FILTER_SANITIZE_MAGIC_QUOTES` (= addslashes), `htmlspecialchars`,
  `htmlentities` before SQL/shell/eval, and `preg_replace("/'/", '')`. None is a substitution for
  that context: a backslash passes all five. The suite calls them safe; E40 does not. (The same
  suite labels `FILTER_SANITIZE_FULL_SPECIAL_CHARS` — which *is* htmlspecialchars — unsafe for SQL:
  its labels disagree with each other here.)
* **`escapeshellarg` (78: 18) — a typo in the corpus.** Every safe file reads
  `$tained = escapeshellarg($tained);` — the misspelt variable is sanitized, `$tainted` reaches
  `system()` raw. The files are vulnerable; the instrument is right.
* **`mysql_real_escape_string` before shell/include/eval** (78: 6, 98: 12, 79: 6) — wrong context.
* **79: `urlencode`/`rawurlencode`/`http_build_query` (30 each)** — the suite puts them into a URL
  attribute, where they are the right substitution; our `html` context does not know it is inside a
  URL. The same sub-context boundary as above, seen from the other side.

## Psalm 5 on the same corpus (`psalm_sard.py`, Psalm 5.26.1, taint analysis)

Psalm has no sink for the removed `mysql_*` API: on CWE_89 as it is, **0 TaintedSql on 9 552 files**.
For the comparison a copy is rewritten to `mysqli_*` (declared, `--mysqli`). Psalm's sources are the
same three superglobals as ours.

| CWE | unsafe: Psalm hit / ours REFUTED | safe: Psalm alarm / ours REFUTED |
|---|---|---|
| 89 sql | 135 / 153 — every Psalm hit is among ours; **the 18 Psalm misses are `mysqli_real_escape_string` OUTSIDE quotes** (the shape of the blog's status.php) | 405 / 90 — Psalm alarms on `settype` (162), anchored `preg_match` (135), `\W`-strip (18) |
| 78 shell | 99 / 96 (its 3 extra are `%d` files it cannot read) | 171 / 114 |
| 98 file | 108 / 102 (same) | 180 / 102 |
| 601 header | 198 / 384 (no `http_redirect` sink) | 54 / 0 |
| 79 html | 252 / 372 | 288 / 168 |
| 95 code | 54 / 51 | 90 / 45 |

Where Psalm is silent it says nothing; where we are silent we say OPEN and name the link.

## DVWA (four levels per flaw; the sink must be in the same file)

| flaw | low | medium | high | impossible |
|---|---|---|---|---|
| sqli | REFUTED | REFUTED (escaped, unquoted) | OPEN (`$_SESSION`) | EARNED |
| sqli_blind | REFUTED | REFUTED | REFUTED | EARNED |
| exec | REFUTED | REFUTED | REFUTED | EARNED (`is_numeric($octet[0])`… — element guards, fixed here) |
| open_redirect | REFUTED | REFUTED | REFUTED | EARNED |
| upload | — | — | — | EARNED (`unlink($temp_file)`: path built BEFORE the extension check — derived-value crediting, fixed here) |
| fi, xss_r | the sink is in `index.php`, another file — nothing judged (boundary) | | | |

## What this pass changed in the instrument (each with a fixture, f37–f47)

1. **An unknown call's result is Z even over constant arguments.** Before, `$obj->get()` and
   `time()` over constants stayed F and four getter shapes came back EARNED. What is *not*
   attacker-controlled is now an allow-list in the catalog (`transparent`: path/time/random/config
   helpers; `narrowing`: array element extraction), grown from what real trees named as weak links.
2. **`sprintf`/`printf` read their literal format**: `%d %u %f %x …` substitute; `%s` carries the
   value and the format's quotes decide; `%c` does not substitute (39 → a quote).
3. **Guards**: pattern/list in a once-assigned variable; `guard(...) == 1 / === true / !== false / > 0`
   wrappers and `(bool)`; `settype($x, "integer")` by reference; `filter_var($x, FILTER_VALIDATE_INT)`
   as a condition and `filter_input(…, FILTER_VALIDATE_INT)` as a substituted source;
   `preg_replace('/[^a-z0-9]/', '', $x)` confines to a class; guards on an element `$octet[0]`
   and through a preserving function (`strtolower($ext) == 'jpg'`).
4. **Literal array keys are their own slots**: `$row['value'] = get_var(); unserialize($row['options'])`
   was REFUTED "path read in full" (two false REFUTED on the blog engine after change 1) — now OPEN.
5. **An escaped part of unknown origin outside quotes is the weak link (OPEN), not a refutation**;
   inside quotes it counts as quoted.
6. **A guard is credited to a value derived before the check** (`$path = $dir . $ext; if (ctype_alpha($ext)) unlink($path)`)
   only when every tainted parent of the value leads back to the checked variable — a direct source
   read, an unchecked sibling element, or a reassigned variable break the credit.

On the blog engine (whole tree, `all` contexts): 36 REFUTED before and after, the same 36;
79 sinks EARNED→OPEN (former false "constants": `func_get_args()`, `scandir()`, `->getParam()`),
8 OPEN→EARNED (`round`, `ceil`). On MindReef: 106 EARNED→OPEN, 87 of them
`$component->renderComponent()` inside compiled Blade views — honest, and noisy; open question.

---

# HTML sub-contexts (2026-09-09, second pass — curator "все да")

The `html` sink now has sub-contexts, read by a small lexer over the **output stream** — inline HTML plus the
literal parts of everything echoed, in order (`atoms.php` class `Html`). Where an attacker-controlled value lands
decides what substitutes it, exactly as quotes decide it for SQL:

| lands in | needs | why plain HTML escaping is not enough |
|---|---|---|
| body text, double-quoted attribute, double-quoted JS string | `html` (encodes `"` `<` `>` `&`) | — this is the base case |
| single-quoted attribute or JS string | `html-sq` (ENT_QUOTES) | `'` ends the value and plain escaping leaves it |
| URL attribute (`href`, `src`, `action`…) | `header` (URL-encoding) | `javascript:` needs no quote or bracket at all |
| unquoted attribute, tag name, attribute name, event handler, `<style>`, `<script>` outside a string, a JS string that is then RUN (`setTimeout('…')`) | `*` only | a space / letter / the script parser defeats every escaper |

`html-sq` is earned by `htmlspecialchars`/`htmlentities` with `ENT_QUOTES` — **the default only since PHP 8.1**, so
`--php 7.4` changes the verdict — and by `FILTER_SANITIZE_*SPECIAL_CHARS`. A JavaScript encoder (`json_encode` with
the `JSON_HEX_*` flags, Laravel `Js::from`) earns `js` inside `<script>`. An output whose position cannot be read
(a standalone function body, or paths that leave the lexer in different states) is judged as body text and **says so**
in the ledger — the status quo, named, not a stricter guess.

## Measured on SARD CWE_79 (html), before → after the sub-context layer

| | unsafe n=4352 (R / O / E) | miss (unsafe→EARNED) | safe n=5728 (R / O / E) | false alarm (safe→REFUTED) |
|---|---|---|---|---|
| flat `html` (first pass) | 432 / 2448 / 1472 | 1472 | 228 / 1372 / 4128 | 228 |
| with sub-contexts | 492 / 2708 / **1152** | **1152** | 120 / 904 / **4704** | **120** |

The remaining 1152 unsafe→EARNED are **all** whitelist/numeric-filter constructions (`ternary_white_list`,
`whitelist_using_array`, `FILTER_SANITIZE_NUMBER_*`) landing in a position the corpus marks unsafe — a value confined
to a fixed set or to digits cannot break out of a tag name or an unquoted attribute either, so our EARNED stands and
the label is the generator's. (One SARD family, `CSS-span_Style_Property_Value`, echoes the literal `checked_data`,
not the tainted variable at all — no sink of ours, correctly.) The 120 remaining false alarms are the same declared
disagreements as elsewhere (`addslashes` and friends are not substitutions) plus `urlencode` inside a *body* position,
where the corpus over-credits it.

## The engine and MindReef with the html layer

* **Blog engine** (`--php 7.4`): REFUTED 36 → 34 — the two that left were `file_get_contents($_FILES[...]['tmp_name'])`,
  and `tmp_name` is written by PHP, not the client (now `F`). The 34 that stand were read in the source: real
  `str_replace("..","")` path filters (bypassable by `....//`), `$_REQUEST`-driven `include`/`$obj->$m()`, and two
  installers that are gated on the live server (`config.php` sets `INSTALLED`, the `.ready` copy 404s). html sinks by
  sub-context: 274 double-quoted attr, 243 text, 117 URL attr, 40 event handler, 25 `<script>`, 23 style, 13 script-code.
* **MindReef** (Laravel, compiled Blade views scanned): 545/3 → 478/70. The 70 OPEN are honest: `href="{{ route(...) }}"`
  (a URL attribute — `e()` is HTML escaping, not URL encoding) and `<svg {{ $attributes }}>` (an attribute-name
  position). The framework's own `renderComponent()` / `yieldContent()` are declared transparent in the overlay, so a
  component is judged in its own compiled file, not counted as an opaque call at every use site.
