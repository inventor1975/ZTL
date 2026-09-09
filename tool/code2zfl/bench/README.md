# bench — code2zfl against labelled corpora (2026-09-09)

The fixtures in `../fixtures` test the questions I thought of. A labelled corpus written by
someone else tests the ones I did not. Two were used, both public, neither committed here:

    git clone --depth 1 https://github.com/stivalet/PHP-Vulnerability-test-suite.git   # SARD / Stivalet, 42 212 files
    git clone --depth 1 https://github.com/digininja/DVWA.git                          # DVWA, four levels per flaw

`sard.py` runs code2zfl over one CWE directory and scores the file verdict (worst sink of the
context) against the directory label. `psalm_sard.py` runs Psalm 5 `--taint-analysis` over the
same directory and joins the three: label, Psalm, ours. Whole suite: ~10 s for us, ~15 s for Psalm.

## How to read the tables below

**This file is layered by pass, not rewritten.** Each section reports the state at the time of that
pass and is kept, so an earlier number is history, not a current claim: the first table measures
**three** sources (the base catalog of the day), the closing table measures **all sixteen**, and a
row may therefore appear with two different figures. The current numbers are always the last table.

Verified on a second reading (main tab, 2026-09-09 12:5x, independent run): the closing table
reproduces exactly — CWE_89 with `stored-input.json`, `unsafe n=912 → REFUTED 804, OPEN 108,
miss 0`; without the overlay the same run gives 357 / 555 / 0 and 210 false alarms against the
first table's 90, which is the three-source figure, not a drift. Reading the first table as
current is the one mistake this file invites, and it nearly caught its own reviewer.

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

---

# All 16 source shapes (2026-09-09, third pass — "надо расширять на все случаи")

The first two passes measured only the three sources both tools see: `$_GET`, `$_POST`, `$_GET` through an
array. The suite has 16 source shapes; the other 13 were coming back OPEN. Two changes close them, and they are
different in kind:

**Mechanism (base catalog — no policy, works with no overlay).** An object of a class defined in the same file
is now followed through its own property states, in call order: `$o = new Input(); $o->getInput()` where the
constructor stored `$_GET` in a property (plain, `$this->p`, or an array element `$this->p['k']` / `$this->p[1]`)
reads back as attacker-controlled. A call that writes an argument by reference (`exec($cmd, $out)` — `$out` is a
source), and a backtick's result, are declared too. Measured effect, base catalog, no overlay: the four
`object-*` shapes went from OPEN to REFUTED across every CWE (CWE_89: +81 each; CWE_79: +204 each), and the
`object-…Getter` **safe** files went OPEN → EARNED (the tracked object shows the escaper). No GET/POST/array-GET
verdict changed. Blog engine: 3 REFUTED unchanged, +45 EARNED (object-method call sites now judged). MindReef:
unchanged.

**Policy (opt-in overlay `overlays/stored-input.json`).** Session data, file contents, process output and
unserialized blobs are Z in the base catalog — the curator's 2026-09-08 decision (stored state stays unproven,
not attacker). `stored-input.json` declares them attacker-controlled instead, which is what the SARD suite
assumes for its remaining nine shapes (`$_SESSION`, `fopen`/`fgets`/`file_get_contents`, `exec`/`system`/`popen`/
`proc_open`/`shell_exec` output, backticks, `unserialize`). It does **not** touch GET/POST (measured: 0 of those
verdicts move when the overlay is added). DB rows stay Z even here; a project overlay can add them.

**Decided 2026-09-09 (curator: "реши сам"): it stays an overlay.** Measured on the blog engine, the overlay adds
42 REFUTED; eight were read in the source and every one is state the application wrote itself — the page cache
(`echo file_get_contents($cachefile)`), the installer's language from the session, a backup tool's own config
through `unserialize`. Z with the link named ("origin not visible here: file_get_contents@L85") is the honest
tier for those; T would assert a fact the file cannot establish. The overlay is for benchmarks and for a project
that declares "nothing stored is trusted" on purpose.

**Review of the pass (Fable over Opus's commit 8b14e22):** one defect found and fixed — the in-file object
dispatch stood *ahead* of the sink check, so an in-file wrapper `class DB { function query($q) {…} }` with an
opaque body would have been inlined instead of judged: a sink lost in silence. Now the call site is judged as the
sink first and the body is followed after (fixture `f56`). No verdict on SARD, the engine or MindReef moved.

Unsafe files found, **all 16 sources**, base catalog + `stored-input.json`:

| CWE | unsafe n | REFUTED | OPEN | miss (→EARNED) | vs 3-source REFUTED before |
|---|---:|---:|---:|---:|---:|
| 89 sql | 912 | 804 | 108 | 0 | was 153 / 171 |
| 78 shell | 624 | 500 | 108 | 16 | was 96 / 117 |
| 98 file | 672 | 532 | 108 | 32 | was 102 / 126 |
| 601 header | 2592 | 1996 | 244 | 352 | was 384 / 486 |
| 79 html | 4352 | 2606 | 594 | 1152 | was 492 / 816 |
| 95 code | 336 | 266 | 66 | 4 | was 51 / 63 |

The OPEN that remain per source are `proc_open` (its output arrives through `$pipes[1]` and a `stream_get_contents`
this file cannot always trace — 39/51 on CWE_89, the rest OPEN, honestly) and the same `%d`/whitelist label
defects as the three-source pass, now multiplied across the other sources. The miss and false-alarm classes are
unchanged in kind — they are the html sub-context ceiling and the five declared sanitizer disagreements, not new
defects. Fixtures: `f54` (stored input, run both with and without the overlay by the stand), `f55` (in-file object
through its property states).

---

# Real projects, not synthetic (2026-09-09, fourth pass — "качай прямо полсотни сразу")

The SARD suite is 42 212 files that one generator wrote. It has no front controller, no class
hierarchy, no framework — so it cannot fail us in the ways a real project does. This pass measures
**50 CMS and framework trees** (`Corpora/php/cms/`, public clones, none committed here), base
catalog, no overlays, `--ctx all`.

    python3 bench/census.py <corpora>/cms out.json      # per project: verdicts, and the NAMED boundaries

## What the corpus found that fixtures could not

Four of the eight defects fixed in this pass were **crashes and silences**, not wrong verdicts —
and a labelled corpus cannot find those, because it only scores the files that came back.

| defect | what it cost | commit |
|---|---|---|
| a conflict summary carries `files` and no `file`; merging it with a plain one put `None` in a sort | CodeIgniter 4, bolt, cakephp: the whole run died | `44e1917` |
| `json_encode` returns `false` on a byte that is not UTF-8 (Symfony names a class with one) — we printed an empty line and exited **0** | symfony, 11 485 files, read as "no facts" | `979516a` |
| PHP 8.1 `gate(...)` puts a `VariadicPlaceholder` where an argument goes | contao, magento2, symfony: fatal, 39 000 files unjudged | `2a4cac5` |
| an unreadable check on a superglobal **element** had nowhere to leave its mark | silent false refutations | `3365f65` |

The third was caught only by running the census twice and diffing: three projects that had judged,
no longer did. A tool that dies loudly is cheap to fix; the one that worries me is the second,
which was silent, and is the reason the encoder now exits non-zero and says why.

## The front controller (`b417a39`)

The largest single source of false accusations in the whole corpus was one project and one shape.
Dolibarr requires `htdocs/main.inc.php` from every page; that requires `htdocs/waf.inc.php`, which
hands `$_SERVER['PHP_SELF']`, `QUERY_STRING` and `$_POST` to a function that dies on bad input.
We could see calls into another file and could not see this, so every page read as unprotected.

| | REFUTED before | after |
|---|---|---|
| dolibarr (4305 files) | 3258 | **218** |
| SuiteCRM (4652) | 493 | 449 |
| chamilo-lms (7351) | 177 | 171 |
| glpi (3084) | 33 | 31 |
| roundcubemail (548) | 19 | 17 |
| moodle (49 719) | 23 | 21 |
| PrestaShop (7747) | 18 | 16 |
| osTicket (717) | 6 | 5 |
| contao (2018) | 1 | 0 |

The credit is always **Z with the checker named** — OPEN, never EARNED. We did not read what that
WAF accepts; we read that something reads the value and may refuse. To turn these into EARNED we
would have to read a NEGATIVE pattern (`preg_match('/[<>"\']/', $v)` → reject), and we read only
positive anchored ones. That is a named boundary, not a silence.

SARD is untouched by all of it — CWE_78, CWE_89, CWE_98 and CWE_79, 25 392 files, every number
identical before and after. The synthetic corpus has no front controller, no `file_exists` guard
and no inheritance, so it could not have told us any of this.

## The 218 that stand in dolibarr, read in the source

Two shapes, both honest:

* `$_SERVER['HTTP_REFERER']` printed into `value="…"` (`htdocs/adherents/card.php:1386` and ~50 more).
  Read in `waf.inc.php`: the gate is called on `PHP_SELF` (line 326), `QUERY_STRING` (334) and
  `$_POST` (338). `HTTP_REFERER` is never handed to it. Recorded as a candidate, not claimed —
  a Referer is chosen by the victim's browser, and no working example has been built.
* `.tpl.php` files with no front controller of their own: they are included BY a page that has one.
  Our graph runs downward (what I include), not upward (who includes me). Fixing it means a reverse
  closure with a universal quantifier — every includer must carry the fact — and is not done.

## What the census ranked next, and what came of it

The census does not only count verdicts; it ranks the NAMED boundary behind every OPEN, across
projects rather than inside one. That ranking chose the rest of this pass, and two of its four
answers were the opposite of what the count suggested.

| boundary | OPEN resting on it alone | what it turned out to be |
|---|---:|---|
| `property` | 26 423 | TWO errors in opposite directions: a literal-key write tainted the whole property, and a computed-key write was dropped entirely (`0ba610d`) |
| `->trans()` and kin | 11 977 | a method call on a foreign object. 8931 of dolibarr's 9991 method names agree across every definition in the tree — offered as `--assume-tree-methods`, measured, and left OFF (`ee2c196`) |
| `param` | 11 938 | honest fog: a framework entry point nothing in the tree calls |
| `unassigned` | 6 276 | `$matches` was the fifth most common name in it — and that was a MISS, not fog (`8140a37`) |

`--assume-tree-methods` is the one place where measurement did not settle the question. Off → on,
`--ctx all`, no overlays: dolibarr EARNED 69 003 → 88 353, OPEN 42 682 → 24 420, REFUTED 218 → 226;
SuiteCRM 3598 → 3955, 7528 → 7372, 440 → 489. It clears 18 262 verdicts of fog and adds 57
accusations that rest on an assumption we cannot check — that the receiver's class is in the tree.
That trade belongs to whoever will act on the findings, so the default does not make it.

## Where the 50 trees stand at the end of the pass

227 924 files, 16 parse errors (0.007 %), **REFUTED 4123 → 1028**, and 26 of the 50 projects have
none at all. The four projects that still carry most of them — SuiteCRM 449, dolibarr 218,
chamilo-lms 171, SMF 37 — are the next reading, not the next patch.

## The developers' own fixes, after this pass (`fixbench.py`, 2026-09-09 late)

The ground truth here is written by nobody on our side: a commit whose message says it fixes a
security problem, run before and after over the files it touched.

    33 plugins, 238 security-fix commits
    CAUGHT 37 · STILL 115 · OPENED 79 · NOISE 3 · NO-SINK 2 · MISSED 2

**Not one line-for-line comparison with the earlier figure.** The pass before this evening measured
31 plugins and 159 commits and gave CAUGHT 14; this one measures 33 and 238. As a share of commits,
15.5 % against 8.8 % — a real move, but the corpora differ and the honest statement is the pair, not
the ratio alone.

**MISSED is still 2, and both were read.** `wp-fastest-cache`, commits `ff806559a` and `ac304ca1e`,
both `inc/wp-polls.php`, both the same shape: the file calls `check_voted($id)`, and `check_voted`
is defined in the *wp-polls* plugin, which is not in this tree. The SQL sink is in another package;
there is nothing here for this instrument to judge. Across 238 commits of ground truth there is
still no case of "we said clean about code that is in the tree".

**NOISE 3 is unread and stays named**: `google-analytics-for-wordpress` `c3ee119c4` and `aa34822e7`
(0 → 1 REFUTED across a footer-check fix), `user-role-editor` `0927510db` (0 → 1 across an interface
rewrite). A fix that produces a shape we dislike is the one class that could hide a defect of ours,
so it is listed rather than summarised away.

