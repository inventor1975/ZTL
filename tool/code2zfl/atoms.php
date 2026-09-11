<?php
/**
 * atoms.php — deterministic PHP atomizer for code2zfl.
 *
 * Reads PHP with nikic/php-parser and emits FACTS about every sink call:
 * which attacker-controlled sources reach its argument, which substitutions
 * (sanitizers) the value passed on EVERY path, where the path went through
 * something this file cannot see (an unknown function, a parameter, a global,
 * a DB row), and whether an escaped fragment sits inside SQL quotes.
 *
 * No model anywhere. The AST is the arbiter; the judge (ZTL core) grades.
 *
 * NEVER EMITS LITERAL VALUES. A string literal contributes exactly two bits:
 * "is its last char a quote" / "is its first char a quote". Secrets in
 * config files therefore cannot leak through this tool's output.
 *
 * Usage:  php atoms.php [--autoload P] [--catalog base.json] [--overlay p.json] FILE... > facts.json
 */
declare(strict_types=1);

$autoload = getenv('CODE2ZFL_AUTOLOAD') ?: (__DIR__ . '/vendor/autoload.php');
$catalogPath = __DIR__ . '/catalog.json';
$overlays = [];
$assumeTree = false;    // may a method call on a FOREIGN object be answered by the tree's definitions of that name?
$files = [];
$phpVersion = null;                       // e.g. 7.4 — legacy syntax the newest grammar refuses
// CROSS-FILE SIGHT, in two passes. A call to a function defined in ANOTHER file was opaque, which is
// honest but blunt: on WordPress it made 1418 esc_attr() calls, 747 esc_url() and every
// wp_check_*() read as unknown. Pass 1 (`--emit-summaries`) walks each definition with its
// parameters marked attacker-controlled and records what the function DOES with them: passes the
// taint on, substitutes it (a sanitizer), reaches a sink with it, or decides a boolean about it (a
// guard). Pass 2 (`--summaries`) reads that and judges calls with it.
//
// The summary is a claim about the callee, so it carries its own grade: a function whose body we
// could not walk in full (budget) is recorded as UNKNOWN, never as clean.
$emitSummaries = false;
$summaryPath = null;
for ($i = 1; $i < $argc; $i++) {
    $a = $argv[$i];
    if ($a === '--autoload') { $autoload = $argv[++$i]; continue; }
    if ($a === '--catalog')  { $catalogPath = $argv[++$i]; continue; }
    if ($a === '--overlay')  { $overlays[] = $argv[++$i]; continue; }
    if ($a === '--assume-tree-methods') { $assumeTree = true; continue; }
    if ($a === '--no-assume-tree-methods') { $assumeTree = false; continue; }
    if ($a === '--php')      { $phpVersion = $argv[++$i]; continue; }
    if ($a === '--emit-summaries') { $emitSummaries = true; continue; }   // pass 1 of cross-file sight
    if ($a === '--summaries') { $summaryPath = $argv[++$i]; continue; }   // pass 2: use what pass 1 learned
    $files[] = $a;
}
if (!is_file($autoload)) {
    fwrite(STDERR, "php-parser autoload not found: $autoload (run `composer install` here or set CODE2ZFL_AUTOLOAD)\n");
    exit(2);
}
require $autoload;

use PhpParser\Node;
use PhpParser\Node\Expr;
use PhpParser\Node\Stmt;
use PhpParser\Node\Scalar;
use PhpParser\ParserFactory;
use PhpParser\Error as ParseError;

/** SILENCE IS THE WORST OUTCOME. json_encode returns false on a byte that is not UTF-8 — Symfony's
 *  Cache/Traits/ValueWrapper.php names its class with one — and we used to print nothing and exit 0,
 *  which the driver read as "no facts". Substitute the bad byte; if it still fails, SAY SO and die. */
function emit(array $d, int $extra): void {
    $j = json_encode($d, JSON_UNESCAPED_UNICODE | JSON_UNESCAPED_SLASHES | JSON_INVALID_UTF8_SUBSTITUTE | $extra);
    if ($j === false) { fwrite(STDERR, "json_encode failed: " . json_last_error_msg() . "\n"); exit(3); }
    echo $j, "\n";
}

// ----------------------------------------------------------------- catalog
function loadJson(string $p): array {
    $d = json_decode((string)file_get_contents($p), true);
    if (!is_array($d)) { fwrite(STDERR, "bad json: $p\n"); exit(2); }
    return $d;
}
function mergeCatalog(array $base, array $over): array {
    foreach ($over as $k => $v) {
        if (str_starts_with((string)$k, '_')) continue;
        if (is_array($v) && isset($base[$k]) && is_array($base[$k])) {
            $isList = array_keys($v) === range(0, count($v) - 1);
            $base[$k] = $isList ? array_values(array_unique(array_merge($base[$k], $v))) : mergeCatalog($base[$k], $v);
        } else {
            $base[$k] = $v;
        }
    }
    return $base;
}
$SUMMARIES = ['functions' => [], 'methods' => []];
$CAT = loadJson($catalogPath);
foreach ($overlays as $o) $CAT = mergeCatalog($CAT, loadJson($o));
if ($summaryPath !== null && is_file($summaryPath)) $SUMMARIES = loadJson($summaryPath);
// Definitions that can REFUSE THE REQUEST (exit / die / throw), by bare name — a statement call to one
// of these is an act of checking. Built once from the summaries; a file's own definitions are added to it.
$ASSUME_TREE = $assumeTree;
$ENDS = [];
foreach (($SUMMARIES['functions'] ?? []) as $n => $r) if (!empty($r['ends'])) $ENDS[$n] = 1;
foreach (($SUMMARIES['methods'] ?? []) as $n => $r) if (!empty($r['ends'])) $ENDS[substr($n, strrpos($n, ':') + 1)] = 1;
// An overlay can only ADD to a merged catalog, and sometimes a project needs the opposite: WordPress's
// $wpdb->delete/insert/update bind their values, so the base catalog's generic `delete` sink is wrong
// there. `not_sinks` / `not_sanitizers` subtract, by exact key (receiver-qualified names allowed).
$NOTSINK = [];                                   // a VETO by receiver: `$wp_the_query->query` is not the base
foreach ($CAT['not_sinks'] ?? [] as $key) {      // catalog's generic `query` sink, though its bare name matches
    $NOTSINK[strtolower($key)] = 1;
    foreach ($CAT['sinks'] as $ctx => &$spec) {
        foreach (['functions', 'methods'] as $slot)
            if (isset($spec[$slot])) $spec[$slot] = array_values(array_filter($spec[$slot], fn($x) => strtolower($x) !== strtolower($key)));
    }
    unset($spec);
}

$lowerKey = fn(string $k) => (str_contains($k, '->') || str_contains($k, '::')) ? preg_replace_callback('/(->|::)([^>:]+)$/', fn($m) => $m[1] . strtolower($m[2]), $k) : strtolower($k);
$SUPER = array_flip($CAT['sources']['superglobals'] ?? []);
$SERVER_KEYS = $CAT['sources']['server_keys'] ?? [];   // which $_SERVER entries an attacker can write
$SERVER_PREFIXES = $CAT['sources']['server_prefixes'] ?? [];
$SRCFN = array_flip(array_map('strtolower', $CAT['sources']['functions'] ?? []));
$SRCMETH = array_flip(array_map($lowerKey, $CAT['sources']['methods'] ?? []));   // "$obj->name", "Class::name", "fn()->name" keys allowed
$SRCBYREF = array_change_key_case($CAT['sources']['byref'] ?? [], CASE_LOWER);   // exec($cmd, $output): argument N is WRITTEN by the call
$SRCSHELL = !empty($CAT['sources']['shell_output']);                              // `backticks` read as an attacker-controlled value
$SANFN = array_change_key_case($CAT['sanitizers']['functions'] ?? [], CASE_LOWER);
$SANMETH = []; foreach ($CAT['sanitizers']['methods'] ?? [] as $k => $v) $SANMETH[$lowerKey($k)] = $v;
$SANCAST = $CAT['sanitizers']['casts'] ?? [];
$TRANSP = []; $TRANSPMETH = [];
foreach ($CAT['transparent'] ?? [] as $f) { if (str_contains($f, '->') || str_contains($f, '::')) $TRANSPMETH[$lowerKey($f)] = 1; else $TRANSP[strtolower($f)] = 1; }
$GUARDS = array_change_key_case($CAT['guards'] ?? [], CASE_LOWER);   // a condition that VERIFIES a value
$INERT = array_flip(array_map('strtolower', $CAT['inert_guards'] ?? []));   // a condition we READ, and it confines nothing
$PRESERV = array_flip(array_map('strtolower', $CAT['preserving'] ?? []));
$NARROW = array_flip(array_map('strtolower', $CAT['narrowing'] ?? []));
// A PROPERTY THE FRAMEWORK FIXES, NOT ONE THE REQUEST WRITES. Declared per project, key = the name the
// ledger would print ($wpdb->prefix), value = the reading that justifies it. This is a claim about
// SOMEBODY ELSE'S SOURCE and it must be quoted there, never asserted here; drop the overlay and the
// property is Z again, as it is by default.
$CONSTPROP = array_change_key_case($CAT['constant_properties'] ?? [], CASE_LOWER);
$SINKFN = []; $SINKMETH = []; $SINKARG = []; $SINKFLAGS = [];
foreach ($CAT['sinks'] as $ctx => $spec) {
    foreach ($spec['functions'] ?? [] as $f) $SINKFN[strtolower($f)] = $ctx;
    foreach ($spec['methods'] ?? [] as $m) $SINKMETH[$lowerKey($m)] = $ctx;
    foreach ($spec['arg'] ?? [] as $f => $ix) $SINKARG[strtolower($f)] = $ix;
    foreach (['echo', 'include', 'eval', 'callable'] as $fl) if (!empty($spec[$fl])) $SINKFLAGS[$fl] = $ctx;
}

// ------------------------------------------------------------------- state
// t: 'T' attacker-controlled on some path (verified) | 'Z' origin not visible here | 'F' constant
// src: [[kind, name, line]]     san: ctx => [fn, line] (held on EVERY path)
// z:   [[why, line]] opaque passes      q: true|false|null  (inside SQL quotes?)
const RANK = ['F' => 0, 'Z' => 1, 'T' => 2];
// dv:  names of the variables this value was DIRECTLY read through — its parents. A guard on $x is credited to a
//      derived $y only when every tainted parent of $y leads back to $x (see derivesOnlyFrom); DVWA upload/impossible
//      builds the temp path from the extension BEFORE checking the extension.
// hc:  html sub-context of the attacker-controlled parts of this string, per possible starting state (worst one);
//      empty for a bare value (its context is wherever it lands).   hf: the lexer state this string leaves behind, per
//      starting state (null = leaves it unchanged; 'unknown' where paths disagree).
// obj: ['class' => name, 'props' => [prop => state]] when the value is an object of a class DEFINED IN THIS FILE, made
//      with `new` here: its methods are inlined on ITS OWN property states, in call order (a strong update per call).
//      Copies of the variable carry copies of the state (value semantics — a named boundary; PHP objects are references).
function stF(): array { return ['t' => 'F', 'src' => [], 'san' => [], 'z' => [], 'q' => null, 'zu' => [], 'nu' => false, 'dv' => [], 'hc' => [], 'hf' => null, 'obj' => null, 'as' => []]; }
function stZ(string $why, int $line): array { return ['t' => 'Z', 'src' => [], 'san' => [], 'z' => [[$why, $line]], 'q' => null, 'zu' => [], 'nu' => false, 'dv' => [], 'hc' => [], 'hf' => null, 'as' => []]; }
function stT(string $kind, string $name, int $line): array { return ['t' => 'T', 'src' => [[$kind, $name, $line]], 'san' => [], 'z' => [], 'q' => null, 'zu' => [], 'nu' => true, 'dv' => ['#src'], 'hc' => [], 'hf' => null, 'as' => []]; }
function objJoin(?array $a, ?array $b): ?array {
    if ($a === null || $b === null || $a['class'] !== $b['class']) return null;
    $props = $a['props'];
    foreach ($b['props'] as $k => $st) $props[$k] = isset($props[$k]) ? join2($props[$k], $st) : $st;
    return ['class' => $a['class'], 'props' => $props];
}
function hcJoin(array $a, array $b): array { $o = $a['hc'] ?? []; foreach ($b['hc'] ?? [] as $k => $c) $o[$k] = Html::worse($o[$k] ?? null, $c); return $o; }
function hfJoin(array $a, array $b): ?array {
    $x = $a['hf'] ?? null; $y = $b['hf'] ?? null;
    if ($x === null && $y === null) return null;
    $o = [];
    foreach (Html::INITS as $k) { $p = $x[$k] ?? $k; $q = $y[$k] ?? $k; $o[$k] = $p === $q ? $p : 'unknown'; }
    return $o;
}
/** Does a state's origin include one of these source rows? (f98-own: a sink or a return is an ARGUMENT's only if it is.) */
function srcMeets(array $src, array $want): bool { foreach ($src as $r) if (in_array($r, $want, true)) return true; return false; }
function dvUnion(array $a, array $b): array { return array_values(array_unique(array_merge($a['dv'] ?? [], $b['dv'] ?? []))); }

function uniq(array $rows): array {
    // The key is built by hand, not by json_encode: these are flat tuples ([kind, name, line] /
    // [why, line]) and this function runs on every path join. MEASURED 2026-09-09 on WordPress
    // `class-wp-html-processor.php` (a switch with 173 cases): json_encode here was the cost.
    $seen = []; $out = [];
    foreach ($rows as $r) {
        $k = is_array($r) ? implode("\x1f", array_map('strval', $r)) : (string)$r;
        if (!isset($seen[$k])) { $seen[$k] = 1; $out[] = $r; }
    }
    return $out;
}
/** JOIN of two paths: may-taint, must-sanitize. */
function join2(array $a, array $b): array {
    $t = RANK[$a['t']] >= RANK[$b['t']] ? $a['t'] : $b['t'];
    $zuX = [];
    if ($a['t'] === 'F') $san = $b['san'];
    elseif ($b['t'] === 'F') $san = $a['san'];
    // a substituted attacker value joined with a value of UNKNOWN origin (a DB row, a directory listing, a call past
    // the depth cap): the substitution stands, the unknown part is the weak link (zu) — not "no substitution seen".
    // Before 2026-09-09 the meet dropped the substitution and a later array_merge read the result as an attacker
    // value "read in full": a false REFUTED on Translation.php:179 after its inputs had been confined to [A-Za-z0-9_-].
    elseif ($a['t'] === 'Z' && !$a['san'] && $b['t'] === 'T' && $b['san']) { $san = $b['san']; $zuX = $a['z']; }
    elseif ($b['t'] === 'Z' && !$b['san'] && $a['t'] === 'T' && $a['san']) { $san = $a['san']; $zuX = $b['z']; }
    else $san = sanMeet($a['san'], $b['san']);
    $qa = $a['t'] === 'F' ? null : $a['q']; $qb = $b['t'] === 'F' ? null : $b['q'];   // constants have no quoting question
    if ($qa === false || $qb === false) $q = false;
    elseif ($qa === null) $q = $qb; elseif ($qb === null) $q = $qa; else $q = true;
    return ['t' => $t, 'src' => uniq(array_merge($a['src'], $b['src'])), 'san' => $san,
            'z' => uniq(array_merge($a['z'], $b['z'])), 'q' => $q,
            'zu' => uniq(array_merge($a['zu'] ?? [], $b['zu'] ?? [], $zuX)), 'nu' => ($a['nu'] ?? false) || ($b['nu'] ?? false), 'dv' => dvUnion($a, $b),
            'hc' => hcJoin($a, $b), 'hf' => hfJoin($a, $b), 'obj' => objJoin($a['obj'] ?? null, $b['obj'] ?? null),
            'as' => uniq(array_merge($a['as'] ?? [], $b['as'] ?? []))];
}
/** MEET of two sanitization maps: '*' (a numeric substitution) covers every context, so it is the identity. */
function sanMeet(array $a, array $b): array {
    if (isset($a['*']) && isset($b['*'])) return $a;
    if (isset($a['*'])) return $b;
    if (isset($b['*'])) return $a;
    return array_intersect_key($a, $b);
}
function joinAll(array $states): array {
    if (!$states) return stF();
    $acc = array_shift($states);
    foreach ($states as $s) $acc = join2($acc, $s);
    return $acc;
}
/** After an unknown function / transformation: taint passes, earned sanitization is dropped. */
/** $keep: 'all' keeps every substitution, 'numeric' keeps only '*' (a number survives any non-introducing
 *  transformation; an escape does not survive substr), 'none' drops them all. */
function through(array $s, ?string $why, int $line, bool $unknown, string $keep = 'none'): array {
    $san = $keep === 'all' ? $s['san'] : ($keep === 'numeric' && isset($s['san']['*']) ? ['*' => $s['san']['*']] : []);
    $out = ['t' => $s['t'], 'src' => $s['src'], 'san' => $san, 'z' => $s['z'], 'q' => $keep === 'all' ? $s['q'] : null, 'zu' => $s['zu'] ?? [],
            'nu' => ($s['nu'] ?? false) || ($keep !== 'all' && $s['t'] === 'T' && !$san), 'dv' => $s['dv'] ?? [],
            'hc' => $s['hc'] ?? [], 'hf' => $keep === 'all' ? ($s['hf'] ?? null) : (($s['hf'] ?? null) === null && ($s['hc'] ?? []) === [] ? null : array_fill_keys(Html::INITS, 'unknown')),
            'as' => $s['as'] ?? []];
    // an UNKNOWN call's result is not visible here even when every argument is a constant: `$obj->get()` reads
    // the object's state, `time()` reads the clock — before 2026-09-09 such a call over constants stayed F and
    // four in-file getter shapes of the SARD suite came back EARNED ("nothing arrives") instead of OPEN
    if ($unknown) { $out['t'] = 'Z'; $out['z'][] = [$why, $line]; $out['nu'] = false; }
    return $out;
}
/** ДОБАВИТЬ подстановку, НЕ трогая остального. `sanitize()` заодно объявляет значение улаженным целиком —
 *  гасит `nu`, чистит `hc`/`hf`. Для УДАЛЕНИЯ ОДНОГО ЗАКРЫВАЮЩЕГО символа это было бы неправдой: значение
 *  по-прежнему может нести `<`, и его собственная разметка текстом не стала. */
function addSan(array $s, array $ctxs, string $fn, int $line): array {
    foreach ($ctxs as $c) $s['san'][$c] = [$fn, $line];
    return $s;
}

function sanitize(array $s, array $ctxs, string $fn, int $line): array {
    // a NUMERIC substitution of the whole value settles every part inside it; a context escape of a
    // built string does not settle a part of unknown origin that may sit outside the quotes
    $zu = in_array('*', $ctxs, true) ? [] : ($s['zu'] ?? []);
    $out = ['t' => $s['t'], 'src' => $s['src'], 'san' => $s['san'], 'z' => $s['z'], 'q' => null, 'zu' => $zu, 'nu' => false, 'dv' => $s['dv'] ?? [],
            'hc' => [], 'hf' => null, 'as' => $s['as'] ?? []];                 // escaped as a whole: its own markup is text now, its parts land wherever the whole lands
    foreach ($ctxs as $c) $out['san'][$c] = [$fn, $line];
    return $out;
}

// -------------------------------------------------------------- html lexer
/** Where in the HTML output a value lands decides what substitutes it — the way quotes decide it for SQL. A small
 *  state machine over the output stream (InlineHTML + the literal parts of what is echoed) tells, for every
 *  attacker-controlled part, whether it sits in body text, a quoted/unquoted attribute value (and of which kind:
 *  URL, event handler, style), a tag or attribute name, <script>, <style> or a comment. A fragment built before it
 *  is echoed cannot know where it will land, so it carries its answer for EVERY possible starting state (a small
 *  vector) and the answer is read off when the fragment is embedded. Literal text is read here and never emitted. */
final class Html {
    const INITS = ['text', 'tagname', 'intag', 'attr-dq-plain', 'attr-sq-plain', 'attr-unq-plain', 'attr-dq-url', 'attr-sq-url',
                   'attr-dq-js', 'attr-sq-js', 'attr-dq-css', 'attr-sq-css', 'script', 'script-sq-plain', 'script-dq-plain',
                   'script-sq-code', 'script-dq-code', 'style', 'comment'];
    /** inside <script>, a quoted string whose text is then RUN as code: no escaping of quotes helps there */
    const JS_CODE_SINK = '/(?:setTimeout|setInterval|eval|Function|execScript|write|writeln|innerHTML|outerHTML|insertAdjacentHTML|href|location|src|action)\s*[(=]\s*$/i';
    const URL_ATTRS = ['href', 'src', 'action', 'formaction', 'data', 'poster', 'background', 'cite', 'longdesc', 'manifest', 'srcset', 'codebase', 'xlink:href'];
    const LEVEL = ['text' => 0, 'attr-dq' => 0, 'script-dq' => 0, 'attr-sq' => 1, 'script-sq' => 1, 'attr-url' => 2];   // anything else: 3 — only a numeric/whitelist substitution
    /** state = [s, flavor, tag, attr, tail, valueSoFar]
     *  `valueSoFar` is the literal text already written INSIDE the current attribute value. It decides
     *  one thing and it matters: a value at the START of a URL attribute can set the scheme
     *  (`javascript:`), and only URL-encoding saves it; a value after `sites.php?action=` cannot —
     *  the scheme is already fixed by the literal, and ordinary HTML escaping is the right substitution.
     *  Measured 2026-09-09 on WordPress `network/sites.php:115`, where esc_attr is correct and we
     *  demanded a URL encoder. */
    public static function init(string $k): array {
        if (preg_match('/^(attr|script)-(dq|sq|unq)-(\w+)$/', $k, $m)) return [$m[1] . '-' . $m[2], $m[3], '', '', '', ''];
        return [$k, 'plain', '', '', '', ''];
    }
    public static function unknown(): array { return ['unknown', 'plain', '', '', '', '']; }
    public static function key(array $st): string {
        return in_array($st[0], ['attr-dq', 'attr-sq', 'attr-unq', 'script-sq', 'script-dq'], true) ? $st[0] . '-' . $st[1] : $st[0];
    }
    public static function needsLex(string $t): bool { return (bool)preg_match('/[<>"\'=\/\s-]/', $t); }
    private static function flavorOf(string $attr): string {
        $n = strtolower($attr);
        if (str_starts_with($n, 'on')) return 'js';
        if ($n === 'style') return 'css';
        return in_array($n, self::URL_ATTRS, true) ? 'url' : 'plain';
    }
    /** Has the literal before this point already fixed the URL's scheme? A `?`, `#`, `/` or an
     *  explicit scheme means the value can no longer choose one. A bare prefix like "foo" cannot be
     *  trusted: `foo` + `javascript:...` is still one token to the browser only if no separator ran,
     *  so we require a separator, not merely non-emptiness. */
    private static function schemeFixed(string $written): bool {
        return (bool)preg_match('~[?#/]|^[a-zA-Z][a-zA-Z0-9+.\-]*:~', $written);
    }

    private static function afterTag(string $tag): string { $t = strtolower($tag); return $t === 'script' ? 'script' : ($t === 'style' ? 'style' : 'text'); }
    public static function advance(array $st, string $t): array {
        [$s, $fl, $tag, $attr, $tail] = $st;
        $val = $st[5] ?? '';                                    // literal already written inside the attribute value
        if ($s === 'unknown') return $st;
        $n = strlen($t);
        for ($i = 0; $i < $n; $i++) {
            $c = $t[$i]; $tail = substr($tail . $c, -40); $ws = ctype_space($c);   // enough tail for `</script`, `-->` and a code-sink name
            if ($s === 'attr-dq' || $s === 'attr-sq' || $s === 'attr-unq') $val = substr($val . $c, -60);
            switch ($s) {
                case 'text':
                    if ($c === '<') { if (substr($t, $i, 4) === '<!--') { $s = 'comment'; $i += 3; $tail = ''; } else $s = 'lt'; }
                    break;
                case 'lt':
                    if (ctype_alpha($c) || $c === '!' || $c === '?') { $s = 'tagname'; $tag = $c; }
                    elseif ($c === '/') { $s = 'tagname'; $tag = ''; }
                    else $s = 'text';
                    break;
                case 'tagname':
                    if (ctype_alnum($c) || $c === '-' || $c === ':' || $c === '_') $tag .= $c;
                    elseif ($c === '>') { $s = self::afterTag($tag); $tag = ''; $tail = ''; }
                    else $s = 'intag';
                    break;
                case 'intag':
                    if ($c === '>') { $s = self::afterTag($tag); $tag = ''; $tail = ''; }
                    elseif (!$ws && $c !== '/') { $s = 'attrname'; $attr = $c; }
                    break;
                case 'attrname':
                    if ($c === '=') $s = 'attr-eq';
                    elseif ($ws) $s = 'attr-after';
                    elseif ($c === '>') { $s = self::afterTag($tag); $tag = ''; $tail = ''; }
                    elseif ($c === '/') $s = 'intag';
                    else $attr .= $c;
                    break;
                case 'attr-after':
                    if ($c === '=') $s = 'attr-eq';
                    elseif ($c === '>') { $s = self::afterTag($tag); $tag = ''; $tail = ''; }
                    elseif (!$ws) { $s = 'attrname'; $attr = $c; }
                    break;
                case 'attr-eq':
                    if ($ws) break;
                    $fl = self::flavorOf($attr);
                    if ($c === '"') { $s = 'attr-dq'; $val = ''; } elseif ($c === "'") { $s = 'attr-sq'; $val = ''; }
                    elseif ($c === '>') { $s = self::afterTag($tag); $tag = ''; $tail = ''; }
                    else $s = 'attr-unq';
                    break;
                case 'attr-dq': if ($c === '"') { $s = 'intag'; $val = ''; } break;
                case 'attr-sq': if ($c === "'") { $s = 'intag'; $val = ''; } break;
                case 'attr-unq':
                    if ($ws) $s = 'intag'; elseif ($c === '>') { $s = self::afterTag($tag); $tag = ''; $tail = ''; }
                    break;
                case 'script':
                    if (strcasecmp(substr($tail, -8), '</script') === 0) { $s = 'tagname'; $tag = ''; }
                    elseif ($c === "'" || $c === '"') { $fl = preg_match(self::JS_CODE_SINK, substr($tail, 0, -1)) ? 'code' : 'plain'; $s = $c === "'" ? 'script-sq' : 'script-dq'; }
                    break;
                case 'script-sq': case 'script-dq':
                    if (strcasecmp(substr($tail, -8), '</script') === 0) { $s = 'tagname'; $tag = ''; }
                    elseif ($c === '\\') { $i++; $tail .= ($t[$i] ?? ''); }
                    elseif ($c === ($s === 'script-sq' ? "'" : '"') || $c === "\n") { $s = 'script'; $fl = 'plain'; }
                    break;
                case 'style':  if (strcasecmp(substr($tail, -7), '</style') === 0) { $s = 'tagname'; $tag = ''; } break;
                case 'comment': if (substr($tail, -3) === '-->') $s = 'text'; break;
            }
        }
        return [$s, $fl, $tag, $attr, $tail, $val];
    }
    /** The sub-context a value landing HERE is in. */
    public static function ctx(array $st): string {
        [$s, $fl] = $st;
        $written = $st[5] ?? '';
        switch ($s) {
            case 'text': return 'text';
            case 'attr-dq': case 'attr-sq':
                if ($fl === 'url' && self::schemeFixed($written)) return $s;   // scheme already decided by the literal
                return $fl === 'plain' ? $s : ($fl === 'url' ? 'attr-url' : ($fl === 'js' ? 'attr-event' : 'attr-style'));
            case 'attr-unq': case 'attr-eq': return 'attr-unquoted';
            case 'lt': case 'tagname': return 'tag-name';
            case 'intag': case 'attrname': case 'attr-after': return 'attr-name';
            case 'script-sq': case 'script-dq': return $fl === 'code' ? 'script-code' : $s;
            case 'unknown': return 'unknown';
            default: return $s;                                             // script, style, comment
        }
    }
    public static function level(string $ctx): int { return $ctx === 'unknown' ? -1 : (self::LEVEL[$ctx] ?? 3); }
    public static function worse(?string $a, string $b): string { return $a === null ? $b : (self::level($b) > self::level($a) ? $b : $a); }
}

// ---------------------------------------------------------------- analyzer
final class Analyzer {
    public array $facts = [];
    public array $includes = [];
    public array $functions = [];
    public string $scope = '(main)';
    private int $loopCap = 4;
    // SIGHT THROUGH CALLS, within one file: a call to a function or `$this->method()` defined here is
    // INLINED with the caller's argument states (depth <= 3, recursion cut), sinks inside are emitted in
    // the caller's context, the joined `return` state comes back. `$this->prop` is a may-join over every
    // assignment in the class, collected on pass 1 and read on pass 2.
    public array $defs = ['fn' => [], 'm' => []];   // name -> Function_ ; class -> name -> ClassMethod
    // class -> parent class, so a method call can find the definition it actually runs. SMF's
    // UnreadReplies extends Unread, and the validation that makes its queries safe lives in the
    // parent: without this the child looked like a textbook injection (measured 2026-09-09).
    public array $parents = [];
    public array $callers = [];                       // 'fn:name' | 'm:Class::name' -> in-file call sites
    public array $props = [];                         // class -> prop -> state
    public int $pass = 1;
    private bool $instanceMode = false;               // inlining a method on a concrete in-file object: its props are updated in place
    private array $callStack = [];
    private array $returns = [];
    private ?string $currentClass = null;
    private int $callDepth = 3;
    // A BUDGET, not just a depth. MEASURED 2026-09-09 on WordPress `class-wp-html-processor.php`
    // (79 methods calling each other): depth 0 → 0.12 s, 1 → 0.62 s, 2 → 6.2 s, 3 → 56 s — each level
    // multiplies the work by the number of in-file calls in a body. Size is not the driver: post.php
    // is larger and takes 1.5 s. Past the budget a call is what it was before any inlining existed —
    // an unknown call, hence Z with the reason named. Slower is acceptable; silent is not.
    private int $inlineBudget = 3000;
    public int $inlineSpent = 0;
    // A NODE BUDGET, for the same reason and with the same honesty. Path joining is quadratic in a
    // `switch` with hundreds of cases over hundreds of variables: WordPress's
    // `module.audio-video.quicktime.php` (350 cases, 191 variables) took 297 s alone, and folding the
    // joins pairwise only brought it to 225. Past the budget the walk STOPS DESCENDING and every
    // value it would have produced is Z — the same answer the tool gave before it could see anything,
    // and the file is flagged so the reader knows the walk was cut. A slow instrument is a nuisance;
    // one that silently looks less far is a liar.
    private int $nodeBudget = 120000;
    public int $nodeSpent = 0;
    // Names this file checks with something we cannot read. Collected in a PRE-PASS, because the
    // check may sit anywhere — nested one level (the WordPress REST shape) or after the sink.
    // The claim is not "checked here" but "this file reads and decides on this value, and what it
    // accepts is not visible from here". Always toward OPEN, never toward EARNED.
    public array $unknownChecked = [];
    /** The same, for a SUPERGLOBAL ELEMENT: `if (their_check($_GET['a'])) { sink($_GET['a']); }`. A slot
     *  never lives in the environment, so the unknown check on it had nowhere to leave its mark and was
     *  dropped in silence — the sink then read as a plain refutation. Measured 2026-09-09. */
    public array $unknownCheckedSlots = [];
    /** Slots (`_REQUEST[option_name]`) a guard has vouched for. A superglobal element never lives in
     *  the environment — it is read straight from the source each time — so a guard on it had no
     *  place to leave its mark, and `preg_match('/^[a-zA-Z_0-9]+$/', $_REQUEST['x'])` counted for
     *  nothing. Measured 2026-09-09 on events-manager 7.4.3, admin/em-options.php:462. */
    private array $guardedSlots = [];

    /** filter flags whose PASS leaves a value in a fixed alphabet: int, float, bool, IP (digits, dots, colons, a-f). EMAIL and URL let a quote through. */
    private const VALIDATE_FIXED = ['FILTER_VALIDATE_INT', 'FILTER_VALIDATE_FLOAT', 'FILTER_VALIDATE_BOOL', 'FILTER_VALIDATE_BOOLEAN', 'FILTER_VALIDATE_IP'];
    /** name -> literal node, for variables assigned EXACTLY ONCE in the file from a literal (`$re = "/^[0-9]+$/"`,
     *  `$allowed = array(...)`): a guard may read them as the fixed set/pattern they are. Filled before the walk. */
    public array $lits = [];

    public function __construct(private array $cat) {}

    private static function mentionsConst(Node $n, string $c): bool {
        if ($n instanceof Expr\ConstFetch) return strtoupper($n->name->toString()) === $c;
        if ($n instanceof Expr\BinaryOp) return self::mentionsConst($n->left, $c) || self::mentionsConst($n->right, $c);
        return false;
    }

    /** THE FLAG ARGUMENT IS A NUMBER, NOT A NAME. htmlspecialchars/htmlentities encode a quote only where the
     *  quote bits are set: ENT_QUOTES (3) both, ENT_COMPAT (2) the double one, ENT_NOQUOTES (0) neither — and a
     *  bare doctype flag (ENT_XML1 = 16, ENT_HTML5 = 48, ENT_HTML401 = 0, ENT_XHTML = 32) also carries quote bits
     *  of zero. Returns 'both' | 'double' | 'none', or null when the expression is not a readable combination of
     *  ENT_* names — a variable or a computed value is not read into, and the catalog's contexts stand as they are.
     *  Measured 2026-09-10: 15 call sites across SMF/SuiteCRM/chamilo/dolibarr pass quote bits of zero. */
    private static function entQuotes(?Node $n): ?string {
        if ($n === null) return null;
        $names = [];
        $walk = function (Node $x) use (&$walk, &$names): bool {
            if ($x instanceof Expr\ConstFetch) { $names[] = strtoupper($x->name->toString()); return true; }
            if ($x instanceof Expr\BinaryOp\BitwiseOr) return $walk($x->left) && $walk($x->right);
            return false;
        };
        if (!$walk($n)) return null;
        foreach ($names as $nm) if (!str_starts_with($nm, 'ENT_')) return null;
        if (in_array('ENT_QUOTES', $names, true)) return 'both';
        if (in_array('ENT_COMPAT', $names, true)) return 'double';
        return 'none';
    }

    /** str_replace(search, replace, $x) / strtr($x, from, to): are search and replace literals (or arrays of literals)
     *  whose REPLACEMENT characters all lie in [A-Za-z0-9_\-,]? Then the call cannot introduce a quote, dot or bracket. */
    private static function replacementIsPlain(Node $call, string $name): bool {
        $ix = $name === 'strtr' ? [1, 2] : [0, 1];
        foreach ($ix as $i) if (!isset($call->args[$i]) || !($call->args[$i] instanceof Node\Arg)) return false;
        $lits = fn(Node $n) => $n instanceof Scalar\String_ ? [$n->value]
              : ($n instanceof Expr\Array_ ? array_map(fn($it) => $it && $it->value instanceof Scalar\String_ ? $it->value->value : null, $n->items) : null);
        $from = $lits($call->args[$ix[0]]->value); $to = $lits($call->args[$ix[1]]->value);
        if ($from === null || $to === null || in_array(null, $from, true) || in_array(null, $to, true)) return false;
        foreach ($to as $t) if (!preg_match('/^[A-Za-z0-9_\-,]*$/', $t)) return false;
        return true;
    }

    /** A literal, or a once-assigned variable standing for one; null otherwise. */
    private function litOf(?Node $n): ?Node {
        if ($n instanceof Expr\Variable && is_string($n->name) && isset($this->lits[$n->name])) return $this->lits[$n->name];
        return self::isLiteral($n) ? $n : null;
    }

    /** `/[^a-zA-Z0-9_]/`, `/\W/`, `/\D/` — a single negated plain class (or its shorthand): with an empty replacement the
     *  output is confined to that class. The `e` flag is refused outright. */
    private static function patternStripsToClass(string $p): bool {
        if (strlen($p) < 3) return false;
        $d = $p[0]; $end = strrpos($p, $d);
        if ($end === false || $end === 0) return false;
        $flags = substr($p, $end + 1); $body = substr($p, 1, $end - 1);
        if (str_contains($flags, 'e')) return false;
        return (bool)preg_match('/^(?:\[\^[A-Za-z0-9_\\\\\-]+\]|\\\\[WD])[+*]?$/', $body);
    }

    /** 0/1 and true/false read as a truth value; anything else is not a truth we credit. */
    private static function truthOf(Node $n): ?bool {
        if ($n instanceof Scalar\Int_) return $n->value === 0 ? false : ($n->value === 1 ? true : null);
        if ($n instanceof Expr\ConstFetch) { $c = strtolower($n->name->toString()); return $c === 'true' ? true : (($c === 'false' || $c === 'null') ? false : null); }
        return null;
    }

    /** Unescaped quote counts of a literal — read for CLASSIFICATION only, never emitted. */
    private static function quoteCounts(?string $s): array {
        if ($s === null || $s === '') return [0, 0];
        $sq = preg_match_all("/(?<!\\\\)'/", $s); $dq = preg_match_all('/(?<!\\\\)"/', $s);
        return [(int)$sq, (int)$dq];
    }

    /** Flatten concat / interpolation into parts: ['lit', firstIsQuote, lastIsQuote] or ['expr', state]. */
    private function parts(Node $e, array &$env): array {
        if ($e instanceof Expr\BinaryOp\Concat) return array_merge($this->parts($e->left, $env), $this->parts($e->right, $env));
        if ($e instanceof Scalar\String_) return [['lit', self::quoteCounts($e->value), $e->value]];
        if ($e instanceof Scalar\InterpolatedString) {
            $out = [];
            foreach ($e->parts as $p) {
                if ($p instanceof Node\InterpolatedStringPart) $out[] = ['lit', self::quoteCounts($p->value), $p->value];
                else $out[] = ['expr', $this->ex($p, $env)];
            }
            return $out;
        }
        return [['expr', $this->ex($e, $env)]];
    }

    private function concat(Node $e, array &$env): array { return $this->concatParts($this->parts($e, $env)); }

    /** sprintf/printf with a LITERAL format: a numeric conversion (%d %u %f %x %b %e %g %o) SUBSTITUTES its
     *  argument — the output is a number whatever came in; %s carries the argument through unchanged and the
     *  literal text around it decides quoting, the same reading as for concatenation. %c is NOT numeric: it
     *  turns an int into a character (39 → a quote). The format literal is never emitted. */
    private function formatParts(Node $fmtNode, array $args, int $line, array &$env): array {
        $segs = [];                                                   // ['txt', string] | ['expr', state]
        if ($fmtNode instanceof Scalar\String_) $segs[] = ['txt', $fmtNode->value];
        else foreach ($fmtNode->parts as $p) $segs[] = $p instanceof Node\InterpolatedStringPart ? ['txt', $p->value] : ['expr', $this->ex($p, $env)];
        $re = '/%(?:(\d+)\$)?[-+ 0]*(?:\'.)?\d*(?:\.\d+)?([bcdeEfFgGosuxX%])/';
        $parts = []; $next = 0;
        foreach ($segs as [$kind, $val]) {
            if ($kind === 'expr') { $parts[] = ['expr', $val]; continue; }
            $pos = 0;
            if (preg_match_all($re, $val, $m, PREG_OFFSET_CAPTURE | PREG_SET_ORDER)) {
                foreach ($m as $mm) {
                    $parts[] = ['lit', self::quoteCounts(substr($val, $pos, $mm[0][1] - $pos)), substr($val, $pos, $mm[0][1] - $pos)];
                    $pos = $mm[0][1] + strlen($mm[0][0]);
                    $conv = $mm[2][0];
                    if ($conv === '%') continue;
                    $ix = ($mm[1][0] !== '' && $mm[1][1] >= 0) ? (int)$mm[1][0] - 1 : $next++;
                    $a = $args[$ix] ?? stZ('sprintf-arg-missing', $line);
                    $parts[] = ['expr', ($conv === 's' || $conv === 'c') ? $a : sanitize($a, ['*'], 'sprintf-%' . $conv, $line)];
                }
            }
            $parts[] = ['lit', self::quoteCounts(substr($val, $pos)), substr($val, $pos)];
        }
        return $this->concatParts($parts);
    }

    /** A literal alone: a constant that may move the html lexer (`echo "<div>"`). */
    private static function litState(string $text): array {
        $st = stF();
        if (!Html::needsLex($text)) return $st;
        $hf = [];
        foreach (Html::INITS as $k) $hf[$k] = Html::key(Html::advance(Html::init($k), $text));
        $st['hf'] = $hf;
        return $st;
    }

    /** Read the html sub-context of a part landing at $cur (a lexer state), then move $cur past it. */
    private static function htmlEmbed(array &$cur, array $part, ?string &$ctx): void {
        $k = Html::key($cur);
        if ($cur[0] === 'unknown') { if ($part['t'] !== 'F') $ctx = Html::worse($ctx, 'unknown'); return; }
        if ($part['hc']) { if (isset($part['hc'][$k])) $ctx = Html::worse($ctx, $part['hc'][$k]); }
        elseif ($part['t'] !== 'F') $ctx = Html::worse($ctx, Html::ctx($cur));
        if ($part['hf'] !== null) { $to = $part['hf'][$k] ?? $k; $cur = $to === 'unknown' ? Html::unknown() : Html::init($to); }
    }

    private function concatParts(array $parts): array {
        $r = $this->concatCore($parts);
        // html: for every possible starting state, where do the attacker-controlled parts land, and what state is left
        $cur = []; foreach (Html::INITS as $k) $cur[$k] = Html::init($k);
        $hc = []; $moved = false;
        foreach ($parts as $p) {
            if ($p[0] === 'lit') { if (Html::needsLex($p[2])) { $moved = true; foreach (Html::INITS as $k) $cur[$k] = Html::advance($cur[$k], $p[2]); } continue; }
            $s = $p[1];
            if ($s['t'] === 'F' && $s['hf'] === null) continue;
            if ($s['hf'] !== null) $moved = true;
            foreach (Html::INITS as $k) { $c = $hc[$k] ?? null; self::htmlEmbed($cur[$k], $s, $c); if ($c !== null) $hc[$k] = $c; }
        }
        $r['hc'] = $hc;
        $r['hf'] = $moved ? array_map(fn($k) => Html::key($cur[$k]), array_combine(Html::INITS, Html::INITS)) : null;
        return $r;
    }

    private function concatCore(array $parts): array {
        $states = []; $qs = []; $sq = 0; $dq = 0; $opaque = false; $zu = []; $sanT = null; $nu = false;
        foreach ($parts as $p) {
            if ($p[0] === 'lit') { $sq += $p[1][0]; $dq += $p[1][1]; continue; }
            $s = $p[1]; $states[] = $s;
            if ($s['t'] === 'F') continue;
            if ($s['t'] === 'Z' && !$s['san']) { $zu = array_merge($zu, $s['z']); }
            if ($s['t'] === 'T') { $sanT = $sanT === null ? $s['san'] : sanMeet($sanT, $s['san']); if (!$s['san'] && !$s['z']) $nu = true; }
            if (isset($s['san']['*'])) continue;                                          // a number needs no quotes
            if (!isset($s['san']['sql-quoted'])) continue;                                // nothing escaped: quoting is moot
            // a fragment that already embedded its escaped part carries the decision; a bare escaped value
            // is decided HERE: inside quotes iff an odd number of unescaped quotes precede it in this string
            $qHere = $s['q'] !== null ? $s['q'] : (($sq % 2 === 1) || ($dq % 2 === 1));
            if ($s['t'] === 'T' || $qHere) $qs[] = $qHere;
            else $zu = array_merge($zu, $s['z']);   // escaped but OUTSIDE quotes and of unknown origin: not settled either way — that part is the weak link, not a refutation
        }
        $r = joinAll($states ?: [stF()]);
        if ($states) {
            if ($sanT !== null) $r['san'] = $sanT;                      // substitution is judged on the attacker-controlled parts
            $r['zu'] = uniq(array_merge($r['zu'] ?? [], $zu));           // parts of unknown origin without a substitution
            $r['nu'] = ($r['nu'] ?? false) || $nu;                       // an attacker part with no substitution, read in full
            $r['q'] = !$qs ? null : (in_array(false, $qs, true) ? false : (in_array(null, $qs, true) ? null : true));
        }
        return $r;
    }

    private function varName(Expr $v): ?string {
        return ($v instanceof Expr\Variable && is_string($v->name)) ? $v->name : null;
    }

    /** `$row['options']` with a literal key is tracked as its OWN slot `row[options]` in the env, beside the whole-array
     *  state `row` (which stays the may-join of every element, for `$row[$k]`, foreach, implode). Before 2026-09-09 a
     *  value written under one key was read back under every other key: `$row['value'] = get_var(); unserialize($row['options'])`
     *  came back REFUTED with "path read in full". The slot name is internal and never emitted (see joinEnv). */
    /** `$this->prop['key']` (literal key) as a property slot name `prop[key]`; null otherwise. */
    /** THE WEAK LINK MUST BE NAMED. Built from identifiers only — never from a literal, so a config value
     *  cannot ride out in a cause. An array key is dropped to `[]`, a computed part is `{expr}`.
     *  MEASURED 2026-09-09: before this, 4357 of SMF's OPEN verdicts named their boundary `property` and
     *  nothing else — almost all of them static fetches (`Config::$packagesdir`, `Utils::$context`). */
    private static function exprName(?Node $e): string {
        if ($e instanceof Expr\Variable) return is_string($e->name) ? '$' . $e->name : '${expr}';
        if ($e instanceof Expr\PropertyFetch || $e instanceof Expr\NullsafePropertyFetch) {
            $op = $e instanceof Expr\NullsafePropertyFetch ? '?->' : '->';
            return self::exprName($e->var) . $op . ($e->name instanceof Node\Identifier ? $e->name->toString() : '{expr}');
        }
        if ($e instanceof Expr\StaticPropertyFetch)
            return ($e->class instanceof Node\Name ? $e->class->toString() : '{expr}') . '::$'
                 . ($e->name instanceof Node\VarLikeIdentifier ? $e->name->toString() : '{expr}');
        if ($e instanceof Expr\ClassConstFetch)
            return ($e->class instanceof Node\Name ? $e->class->toString() : '{expr}') . '::'
                 . ($e->name instanceof Node\Identifier ? $e->name->toString() : '{expr}');
        if ($e instanceof Expr\ArrayDimFetch) return self::exprName($e->var) . '[]';
        if ($e instanceof Expr\MethodCall || $e instanceof Expr\NullsafeMethodCall)
            return self::exprName($e->var) . '->' . ($e->name instanceof Node\Identifier ? $e->name->toString() : '{expr}') . '()';
        if ($e instanceof Expr\StaticCall)
            return ($e->class instanceof Node\Name ? $e->class->toString() : '{expr}') . '::'
                 . ($e->name instanceof Node\Identifier ? $e->name->toString() : '{expr}') . '()';
        if ($e instanceof Expr\FuncCall) return ($e->name instanceof Node\Name ? $e->name->toString() : '{expr}') . '()';
        return '{expr}';
    }

    private static function propArraySlot(Expr $n): ?string {
        if (!($n instanceof Expr\ArrayDimFetch) || !($n->var instanceof Expr\PropertyFetch)) return null;
        $pf = $n->var; $d = $n->dim;
        if (!($pf->var instanceof Expr\Variable) || $pf->var->name !== 'this' || !($pf->name instanceof Node\Identifier)) return null;
        if ($d instanceof Scalar\String_) return $pf->name->toString() . '[' . $d->value . ']';
        if ($d instanceof Scalar\Int_) return $pf->name->toString() . '[' . $d->value . ']';
        return null;
    }

    private static function slot(Expr $target): ?string {
        if (!($target instanceof Expr\ArrayDimFetch) || !($target->var instanceof Expr\Variable) || !is_string($target->var->name)) return null;
        $d = $target->dim;
        if ($d instanceof Scalar\String_) return $target->var->name . '[' . $d->value . ']';
        if ($d instanceof Scalar\Int_) return $target->var->name . '[' . $d->value . ']';
        return null;
    }

    /** The html output stream's lexer state at this point of the file (InlineHTML and echoed literals move it). */
    public array $hs = ['text', 'plain', '', '', ''];

    private function sinkFact(string $ctx, string $fn, int $line, array $s, ?string $hctx = null): void {
        $this->facts[] = ['ctx' => $ctx, 'fn' => $fn, 'line' => $line, 'scope' => $this->scope,
                          't' => $s['t'], 'src' => $s['src'], 'san' => $s['san'], 'z' => $s['z'], 'q' => $s['q'], 'zu' => $s['zu'] ?? [], 'nu' => $s['nu'] ?? false, 'as' => $s['as'] ?? [],
                          'hctx' => $hctx];
    }

    /** Something is written to the html output: read where its attacker-controlled parts land, move the stream on. */
    private function output(string $fn, int $line, array $s): void {
        global $SINKFLAGS, $SINKFN;
        $ctx = null;
        self::htmlEmbed($this->hs, $s, $ctx);
        $sink = $SINKFLAGS['echo'] ?? ($SINKFN['print'] ?? null);
        if ($sink !== null) $this->sinkFact($sink, $fn, $line, $s, $s['t'] !== 'F' ? ($ctx ?? 'unknown') : null);
    }

    private function callName(Node $c): ?string {
        if ($c instanceof Expr\FuncCall && $c->name instanceof Node\Name) return strtolower($c->name->toString());
        // a static call's method is an Identifier, not a Name — before 2026-09-08 every Class::method() fell
        // through as a dynamic call, so DB::select() was never a sink
        if ($c instanceof Expr\StaticCall && $c->name instanceof Node\Identifier) return strtolower($c->name->toString());
        if (($c instanceof Expr\MethodCall || $c instanceof Expr\NullsafeMethodCall) && $c->name instanceof Node\Identifier) return strtolower($c->name->toString());
        return null;
    }

    private function args(Node $c, array &$env): array {
        $out = [];
        foreach ($c->args as $a) {
            if ($a instanceof Node\Arg) $out[] = $this->ex($a->value, $env);
            else $out[] = stZ('spread-arg', $c->getStartLine());
        }
        return $out;
    }

    /** Evaluate an expression to a taint state; records sinks and assignments on the way. */
    public function ex(?Node $e, array &$env): array {
        if (++$this->nodeSpent > $this->nodeBudget) return stZ('node-budget', $e ? $e->getStartLine() : 0);
        global $SUMMARIES, $SUPER, $SERVER_KEYS, $SERVER_PREFIXES, $GUARDS, $SRCFN, $SRCMETH, $SRCBYREF, $SRCSHELL, $SANFN, $SANMETH, $SANCAST, $TRANSP, $TRANSPMETH, $PRESERV, $NARROW, $SINKFN, $SINKMETH, $SINKARG, $SINKFLAGS, $NOTSINK, $ASSUME_TREE, $CONSTPROP;
        if ($e === null) return stF();
        $line = $e->getStartLine();

        if ($e instanceof Scalar\String_) return self::litState($e->value);
        if ($e instanceof Scalar\Int_ || $e instanceof Scalar\Float_
            || $e instanceof Scalar\MagicConst || $e instanceof Expr\ConstFetch || $e instanceof Expr\ClassConstFetch) return stF();
        if ($e instanceof Scalar\InterpolatedString || $e instanceof Expr\BinaryOp\Concat) return $this->concat($e, $env);

        if ($e instanceof Expr\Variable) {
            if (!is_string($e->name)) { return stZ('variable-variable', $line); }
            if (isset($this->unknownChecked[$e->name]) && !isset($SUPER[$e->name])) {
                $st = $env[$e->name] ?? stZ('unassigned:$' . $e->name, $line);
                if ($st['t'] !== 'F') return through($st, 'guarded-by:' . $this->unknownChecked[$e->name], $line, true, 'all');
            }
            if (isset($SUPER[$e->name])) return stT('superglobal', '$' . $e->name, $line);
            if ($e->name === 'this') return stF();
            $whole = self::envWhole($env, $e->name);
            if ($whole === null) return stZ('unassigned:$' . $e->name, $line);
            $st = $whole; $st['dv'] = [$e->name]; return $st;                   // the DIRECT parent of what is read is this variable
        }
        if ($e instanceof Expr\ArrayDimFetch) {
            $this->ex($e->dim, $env);
            // $_SERVER is attacker-written only in part: HTTP_* headers, the request line and path — not
            // REMOTE_ADDR or SERVER_*. A literal key is CLASSIFIED here and never emitted.
            $slotKey = self::slot($e);
            // A SUPERGLOBAL SLOT CAN BE OVERWRITTEN, and then it is no longer the request. SMF's
            // Unread.php does exactly that: `$_REQUEST['sort'] = $this->sort_methods[$_REQUEST['sort']]`
            // replaces the value with one from a fixed map before any query sees it. Reading the
            // source unconditionally made every later use look attacker-controlled.
            if ($slotKey !== null && array_key_exists($slotKey, $env)) return $env[$slotKey];
            // A CHECK WE CANNOT READ, on the slot itself — from this file, or from a file it includes.
            // It must be consulted BEFORE the per-superglobal branches below, which return early.
            if ($slotKey !== null && isset($this->unknownCheckedSlots[$slotKey])) {
                $base = $this->ex($e->var, $env);
                if (($base['t'] ?? 'F') !== 'F') return through($base, 'guarded-by:' . $this->unknownCheckedSlots[$slotKey], $line, true, 'all');
            }
            if ($slotKey !== null && isset($this->guardedSlots[$slotKey])) {
                [$ctxs, $fn, $ln] = $this->guardedSlots[$slotKey];
                $base = $this->ex($e->var, $env);
                if (($base['t'] ?? 'F') !== 'F')
                    return $ctxs === ['?'] ? through($base, 'guarded-by:' . $fn, $ln, true, 'all') : sanitize($base, $ctxs, $fn, $ln);
            }
            // $_FILES: the browser chooses `name` and `type`; PHP itself writes `tmp_name`, `size` and
            // `error`. Treating the temporary path as attacker-controlled made every upload validator
            // read as a file-inclusion hole (events-manager 7.4.3, three of nine verdicts).
            if ($e->var instanceof Expr\Variable && $e->var->name === '_FILES' && $e->dim instanceof Scalar\String_) {
                // $_FILES['f']['tmp_name'] parses as ($_FILES['f'])['tmp_name'] — the inner fetch is here
            }
            if ($e->var instanceof Expr\ArrayDimFetch && $e->var->var instanceof Expr\Variable
                && $e->var->var->name === '_FILES' && $e->dim instanceof Scalar\String_
                && in_array($e->dim->value, ['tmp_name', 'size', 'error'], true)) {
                return stF();
            }
            if ($e->var instanceof Expr\Variable && $e->var->name === '_SERVER' && isset($SUPER['_SERVER'])) {
                if ($e->dim instanceof Scalar\String_) {
                    $k = $e->dim->value;
                    $hot = in_array($k, $SERVER_KEYS, true);
                    foreach ($SERVER_PREFIXES as $pfx) if (str_starts_with($k, $pfx)) $hot = true;
                    return $hot ? stT('superglobal', '$_SERVER', $line) : stF();
                }
                return stT('superglobal', '$_SERVER', $line);                       // a computed key: assume the worst
            }
            // $_FILES['f']['tmp_name'|'size'|'error'] are written by PHP itself; 'name' and 'type' come from the client
            if ($e->var instanceof Expr\ArrayDimFetch && $e->var->var instanceof Expr\Variable && $e->var->var->name === '_FILES' && isset($SUPER['_FILES'])
                && $e->dim instanceof Scalar\String_ && in_array($e->dim->value, ['tmp_name', 'size', 'error', 'full_path'], true) && $e->dim->value !== 'full_path') return stF();
            // $this->prop['key']: read the element's own slot, else the whole property
            if ($this->currentClass !== null && ($ps = self::propArraySlot($e)) !== null && $e->var instanceof Expr\PropertyFetch) {
                $pn = $e->var->name->toString();
                if (isset($this->props[$this->currentClass][$ps])) return $this->props[$this->currentClass][$ps];
                if (isset($this->props[$this->currentClass][$pn])) return $this->props[$this->currentClass][$pn];
                return stZ('property:$this->' . $pn, $line);
            }
            $sl = self::slot($e);
            if ($sl !== null && isset($env[$sl])) { $st = $env[$sl]; $st['dv'] = [$sl]; return $st; }   // this key was written here: read that, not the whole array
            // AN ELEMENT NEVER WRITTEN HERE reads the array's BULK state — what was assigned to the name
            // itself — and NOT the join with its sibling slots: `$row['options']` after
            // `$row['value'] = $_GET['v']` is still the database row, not the request (f43).
            if ($sl !== null && $e->var instanceof Expr\Variable && is_string($e->var->name) && isset($env[$e->var->name])) {
                $st = $env[$e->var->name]; $st['dv'] = [$sl]; return $st;
            }
            // A LITERAL KEY WITH NEITHER ITS OWN SLOT NOR A BULK STATE is not the join of its siblings:
            // an array built only element-wise says nothing about a key nobody wrote. Reading `$GLOBALS['b']`
            // after `$GLOBALS['a'] = $_GET['x']` is unknown, not attacker-controlled.
            if ($sl !== null && $e->var instanceof Expr\Variable && is_string($e->var->name) && !isset($SUPER[$e->var->name]))
                return stZ('unassigned:$' . $e->var->name . '[]', $line);
            $base = $this->ex($e->var, $env);
            return $base;
        }
        if ($e instanceof Expr\PropertyFetch || $e instanceof Expr\NullsafePropertyFetch || $e instanceof Expr\StaticPropertyFetch) {
            if ($e instanceof Expr\PropertyFetch && $e->var instanceof Expr\Variable && $e->var->name === 'this'
                && $e->name instanceof Node\Identifier && $this->currentClass !== null) {
                $pn = $e->name->toString();
                $whole = $this->propWhole($this->currentClass, $pn);
                if ($whole !== null) return $whole;
                return stZ('property:$this->' . $pn, $line);
            }
            // another object's property: name the object, so the ledger says WHICH boundary this is
            $pn = self::exprName($e);
            if (isset($CONSTPROP[strtolower($pn)])) return stF();   // declared, with its reading, in the project overlay
            return stZ('property:' . $pn, $line);
        }
        if ($e instanceof Expr\Array_) {
            $st = [];
            foreach ($e->items as $it) { if ($it === null) continue; if ($it->key) $st[] = $this->ex($it->key, $env); $st[] = $this->ex($it->value, $env); }
            return joinAll($st ?: [stF()]);
        }
        if ($e instanceof Expr\Assign || $e instanceof Expr\AssignRef) {
            $rhs = $this->ex($e->expr, $env);
            $this->assignTo($e->var, $rhs, $env, $line, $e->expr);
            return $rhs;
        }
        if ($e instanceof Expr\AssignOp) {
            $rhs = $this->ex($e->expr, $env);
            $cur = $this->ex($e->var, $env);
            if ($e instanceof Expr\AssignOp\Concat) {
                $r = join2($cur, $rhs);
            } else { $r = join2($cur, $rhs); $r['san']['*'] = ['arith', $line]; }
            $self = $this->varName($e->var) ?? self::slot($e->var);
            if ($self !== null) $r['dv'] = array_values(array_diff($r['dv'] ?? [], [$self]));   // `$t .= x`: the old $t is not a parent of itself
            $this->assignTo($e->var, $r, $env, $line);
            return $r;
        }
        if ($e instanceof Expr\Ternary) {
            $c = $this->ex($e->cond, $env);
            // A TERNARY IS AN `if`, AND ITS CONDITION GUARDS ITS BRANCHES. `$show = in_array(trim($_REQUEST['show']),
            // ['all','none']) ? $_REQUEST['show'] : 'all';` is the ordinary PHP way to validate-or-default, and we read
            // the guard only from If_/ElseIf_/While_/Do_ — so the same check written as a statement earned and written
            // as a ternary refuted. chamilo's link.php:79, 14 verdicts behind it. Measured 2026-09-09.
            $g = $this->guards($e->cond);
            // A GUARD LIVES IN ITS BRANCH (f90, 2026-09-10). Guards on a superglobal slot are kept in
            // $this->guardedSlots, not in the env, so they must be saved and restored around each branch:
            // before this, the true branch's guard was also seen by the false branch AND by every later
            // read in the file — SuiteCRM WizardMarketing.php:789 was EARNED on a check made in a ternary
            // 480 lines earlier.
            $gs0 = $this->guardedSlots;
            $envT = $env; $envF = $env;
            $this->applyGuards($g['true'], $envT);
            $this->applyUnknownGuards($g['unknown'] ?? [], $envT);
            $this->applyUnknownGuards($g['unknown_true'] ?? [], $envT);
            $a = $e->if ? $this->ex($e->if, $envT) : $c;
            $this->guardedSlots = $gs0;
            $this->applyGuards($g['false'], $envF);
            $b = $this->ex($e->else, $envF);
            $this->guardedSlots = $gs0;
            return join2($a, $b);
        }
        if ($e instanceof Expr\BinaryOp\Coalesce) return join2($this->ex($e->left, $env), $this->ex($e->right, $env));
        if ($e instanceof Expr\BinaryOp) {
            $l = $this->ex($e->left, $env); $r = $this->ex($e->right, $env);
            if ($e instanceof Expr\BinaryOp\Plus || $e instanceof Expr\BinaryOp\Minus || $e instanceof Expr\BinaryOp\Mul
                || $e instanceof Expr\BinaryOp\Div || $e instanceof Expr\BinaryOp\Mod || $e instanceof Expr\BinaryOp\Pow) {
                $j = join2($l, $r); $j['san'] = ['*' => ['arith', $line]]; return $j;       // numeric result: substitution
            }
            if ($e instanceof Expr\BinaryOp\BitwiseAnd || $e instanceof Expr\BinaryOp\BitwiseOr || $e instanceof Expr\BinaryOp\BitwiseXor) {
                return through(join2($l, $r), null, $line, false, 'none');                  // bytewise on strings
            }
            return stF();                                                                    // comparisons, logic, spaceship
        }
        if ($e instanceof Expr\UnaryMinus || $e instanceof Expr\UnaryPlus) { $s = $this->ex($e->expr, $env); $s['san'] = ['*' => ['arith', $line]]; return $s; }
        if ($e instanceof Expr\BooleanNot || $e instanceof Expr\Isset_ || $e instanceof Expr\Empty_ || $e instanceof Expr\Instanceof_) {
            foreach (($e instanceof Expr\Isset_ ? $e->vars : [$e->expr]) as $x) $this->ex($x, $env);
            return stF();
        }
        if ($e instanceof Expr\Cast) {
            $s = $this->ex($e->expr, $env);
            if ($e instanceof Expr\Cast\Int_)    return sanitize($s, $SANCAST['int'] ?? ['*'], '(int)', $line);
            if ($e instanceof Expr\Cast\Double)  return sanitize($s, $SANCAST['double'] ?? ['*'], '(float)', $line);
            if ($e instanceof Expr\Cast\Bool_)   return sanitize($s, $SANCAST['bool'] ?? ['*'], '(bool)', $line);
            return through($s, null, $line, false, 'all');
        }
        if ($e instanceof Expr\Include_) {
            $s = $this->ex($e->expr, $env);
            if ($s['t'] !== 'F') { $this->includes[] = $line; if (isset($SINKFLAGS['include'])) $this->sinkFact($SINKFLAGS['include'], 'include', $line, $s); }
            return stZ('include-result', $line);
        }
        if ($e instanceof Expr\Eval_) {
            $s = $this->ex($e->expr, $env);
            if (isset($SINKFLAGS['eval'])) $this->sinkFact($SINKFLAGS['eval'], 'eval', $line, $s);
            return stZ('eval-result', $line);
        }
        if ($e instanceof Expr\Print_) {
            $s = $this->ex($e->expr, $env);
            if (isset($SINKFN['print'])) $this->output('print', $line, $s);
            return stF();
        }
        if ($e instanceof Expr\Closure || $e instanceof Expr\ArrowFunction) {
            $inner = [];
            if ($e instanceof Expr\Closure) { foreach ($e->uses as $u) { $n = $this->varName($u->var); if ($n !== null) $inner[$n] = $env[$n] ?? stZ('unassigned:$' . $n, $line); } }
            foreach ($e->params as $p) { $n = $this->varName($p->var); if ($n !== null) $inner[$n] = stZ('param:$' . $n, $line); }
            $save = $this->scope; $this->scope = $save . '/closure@' . $line;
            if ($e instanceof Expr\Closure) $this->walk($e->stmts, $inner); else $this->ex($e->expr, $inner);
            $this->scope = $save;
            return stF();
        }
        if ($e instanceof Expr\New_) {
            if ($e->class instanceof Expr) {                                   // new $classname(...)
                $cls = $this->ex($e->class, $env);
                if (isset($SINKFLAGS['callable'])) $this->sinkFact($SINKFLAGS['callable'], 'new-$class', $line, $cls);
            }
            $st = $this->args($e, $env);
            if ($e->class instanceof Node\Name) {
                $cn = $e->class->getLast();
                if (isset($this->defs['m'][$cn])) {                              // a class of THIS file: an object with its own property states
                    $inst = ['class' => $cn, 'props' => []];
                    if (isset($this->defs['m'][$cn]['__construct'])) $this->instanceCall($inst, '__construct', $st, $line);
                    $o = stF(); $o['obj'] = $inst; return $o;
                }
            }
            return joinAll($st) ['t'] === 'F' ? stF() : stZ('new', $line);
        }
        if ($e instanceof Expr\Match_) {
            $this->ex($e->cond, $env); $st = [];
            foreach ($e->arms as $arm) { foreach ($arm->conds ?? [] as $c) $this->ex($c, $env); $st[] = $this->ex($arm->body, $env); }
            return joinAll($st ?: [stF()]);
        }
        if ($e instanceof Expr\FuncCall || $e instanceof Expr\StaticCall || $e instanceof Expr\MethodCall || $e instanceof Expr\NullsafeMethodCall) {
            $isMethod = $e instanceof Expr\MethodCall || $e instanceof Expr\NullsafeMethodCall;
            $recvState = $isMethod ? $this->ex($e->var, $env) : null;
            $name = $this->callName($e);
            $args = $this->args($e, $env);
            $recv = null;
            if ($isMethod && $e->var instanceof Expr\Variable && is_string($e->var->name)) $recv = '$' . $e->var->name . '->' . $name;
            elseif ($isMethod && $e->var instanceof Expr\FuncCall && $e->var->name instanceof Node\Name) $recv = strtolower($e->var->name->toString()) . '()->' . $name;
            elseif ($e instanceof Expr\StaticCall && $e->class instanceof Node\Name) $recv = $e->class->getLast() . '::' . $name;
            // Db::$db->query(), $this->db->query(): a singleton reached through a property. Without this the
            // key falls back to the bare method name, and an overlay written as `Db::$db->escape_string`
            // matched nothing at all — measured on SMF 2026-09-09, where the whole overlay was inert.
            elseif ($isMethod && ($e->var instanceof Expr\StaticPropertyFetch || $e->var instanceof Expr\PropertyFetch)) $recv = self::exprName($e->var) . '->' . $name;
            $qual = fn(array $table) => ($recv !== null && isset($table[$recv])) ? $table[$recv] : ($table[$name] ?? null);
            // sprintf/printf with a literal format: the format decides substitution (%d) and quoting (%s)
            $fmt = null;
            if (!$isMethod && ($name === 'sprintf' || $name === 'printf')
                && (($e->args[0]->value ?? null) instanceof Scalar\String_ || ($e->args[0]->value ?? null) instanceof Scalar\InterpolatedString))
                $fmt = $this->formatParts($e->args[0]->value, array_slice($args, 1), $line, $env);
            // settype($x, "integer"): by reference, the variable itself is a number from here on (a literal type name is
            // read for classification only)
            if (!$isMethod && $name === 'settype' && ($e->args[0]->value ?? null) instanceof Expr\Variable && is_string($e->args[0]->value->name)
                && ($e->args[1]->value ?? null) instanceof Scalar\String_
                && in_array(strtolower($e->args[1]->value->value), ['int', 'integer', 'float', 'double', 'bool', 'boolean'], true)) {
                $vn = $e->args[0]->value->name;
                $env[$vn] = sanitize($env[$vn] ?? stF(), ['*'], 'settype', $line);
                return stF();
            }
            if ($name === null) {                                             // $fn(...) / $obj->$m(...)
                $callee = null;
                if (!$isMethod && $e instanceof Expr\FuncCall) $callee = $this->ex($e->name, $env);
                elseif ($isMethod && $e->name instanceof Expr) $callee = $this->ex($e->name, $env);
                if ($callee !== null && isset($SINKFLAGS['callable'])) $this->sinkFact($SINKFLAGS['callable'], '$callable()', $line, $callee);
                return through(joinAll($args ?: [stF()]), 'dynamic-call', $line, true);
            }
            // sinks first: the argument as it ARRIVES
            $sinkCtx = $isMethod ? $qual($SINKMETH) : ($e instanceof Expr\StaticCall ? ($qual($SINKMETH) ?? ($SINKFN[$name] ?? null)) : ($SINKFN[$name] ?? null));
            // `not_sinks` names an ACT, and the receiver is part of the act. Subtracting only by bare name
            // could not say "this project's $wp_the_query->query is not SQL" without also unsaying $db->query.
            if ($sinkCtx !== null && $recv !== null && isset($NOTSINK[strtolower($recv)])) $sinkCtx = null;
            if ($sinkCtx !== null) {
                // ONE CALL CAN CARRY THE DANGER IN SEVERAL ARGUMENTS, and judging only the first hides the rest.
                // `mail($to, $subject, $body, $headers)` folds THREE of its four into the message headers;
                // `copy($from, $to)` and `rename($from, $to)` are two paths, not one. So `arg` in the catalog
                // may be a single index or a LIST of them, and every listed argument is judged.
                $ixs = $SINKARG[$name] ?? 0;
                if (!is_array($ixs)) $ixs = [$ixs];
                if ($fmt !== null && $name === 'printf') $this->output('printf', $line, $fmt);   // what is printed is the FORMATTED string
                elseif ($name === 'printf' && isset($args[0])) $this->output('printf', $line, $args[0]);
                else foreach ($ixs as $ix) if (isset($args[$ix])) $this->sinkFact($sinkCtx, ($isMethod ? '->' : '') . $name, $line, $args[$ix]);
            }
            // SINKS ARE JUDGED FIRST, then a call into a class of this file is followed inside. Before 2026-09-09 12:30 the
            // dispatch below stood ahead of the sink check: an in-file wrapper `class DB { function query($q) {…} }` with a
            // body this file cannot read would have been inlined INSTEAD of judged — a sink lost in silence (Fable's review
            // of the Opus pass; fixture f56).
            // an object of a class defined in THIS file: the method runs on that object's own property states, in call order
            if ($isMethod && $name !== null && ($recvState['obj'] ?? null) !== null && isset($this->defs['m'][$recvState['obj']['class']][$name])) {
                $inst = $recvState['obj'];
                $r = $this->instanceCall($inst, $name, $args, $line);
                $vn = $e->var instanceof Expr\Variable ? $this->varName($e->var) : null;
                if ($vn !== null && isset($env[$vn])) $env[$vn]['obj'] = $inst;          // the object was changed by the call
                return $r;
            }
            if ($e instanceof Expr\StaticCall && $name !== null && $e->class instanceof Node\Name
                && !in_array(strtolower($e->class->toString()), ['self', 'static', 'parent'], true)
                && isset($this->defs['m'][$e->class->getLast()][$name])) {           // Foo::bar() of a class defined here: class-wide property states
                $cn = $e->class->getLast();
                $saveClass = $this->currentClass; $this->currentClass = $cn;
                $r = $this->inline($this->defs['m'][$cn][$name], $args, $line, 'm:' . $cn . '::' . $name);
                $this->currentClass = $saveClass;
                return $r;
            }
            // preg_match($pat, $subject, $matches) WRITES the subject's own substrings into $matches. We
            // used to read $matches as `unassigned` — Z, OPEN — which is a MISS when the pattern confines
            // nothing: `preg_match('/x(.*)/', $_SERVER['REQUEST_URI'], $m)` puts the request in $m[1].
            // A capture is a narrowing of the subject, so only `*` survives it; a pattern we read AND find
            // tight is itself the substitution, by the same rule patternIsTight already applies to guards.
            // MEASURED 2026-09-09: `$matches` was the 5th most common unassigned name across 50 projects.
            if (!$isMethod && ($name === 'preg_match' || $name === 'preg_match_all') && isset($e->args[2])
                && $e->args[2] instanceof Node\Arg && isset($e->args[1])) {
                $subj = $this->ex($e->args[1]->value, $env);
                $got = self::patternConfines($e->args[0]->value ?? null)
                     ? sanitize($subj, ['*'], 'preg_match:confined', $line)
                     : through($subj, null, $line, false, 'numeric');   // a substring: only `*` survives, as with substr
                $this->assignTo($e->args[2]->value, $got, $env, $line);
            }
            // a call that WRITES an attacker-controlled value into an argument: exec($cmd, $output)
            if (!$isMethod && isset($SRCBYREF[$name])) {
                $ix = (int)$SRCBYREF[$name];
                if (isset($e->args[$ix]) && $e->args[$ix] instanceof Node\Arg) $this->assignTo($e->args[$ix]->value, stT('fn', $name . '#' . $ix, $line), $env, $line);
            }
            // sources
            if ($isMethod ? ($qual($SRCMETH) !== null) : ($e instanceof Expr\StaticCall ? ($qual($SRCMETH) !== null || isset($SRCFN[$name])) : isset($SRCFN[$name]))) {
                $src = stT('fn', $recv ?? (($isMethod ? '->' : '') . $name), $line);
                $flt = (!$isMethod && $name === 'filter_input') ? ($e->args[2]->value ?? null) : null;   // filter_input(INPUT_GET, 'id', FILTER_VALIDATE_INT)
                $fname = $flt instanceof Expr\ConstFetch ? strtoupper($flt->name->toString()) : '';
                return in_array($fname, self::VALIDATE_FIXED, true) ? sanitize($src, ['*'], 'filter_input:' . $fname, $line) : $src;
            }
            // `array_map('intval', $ids)` APPLIES intval TO EVERY ELEMENT. With a LITERAL callback naming
            // a function we already know, the whole array gets that function's treatment — the commonest
            // shape of it, `array_map('intval', (array) $_POST['id'])` before `IN ('".implode("','",$ids)."')`,
            // is how chamilo builds a safe list and we called it an injection 15 times. Measured 2026-09-09.
            // A callback we cannot read stays what it was: an opaque call, and a callable sink besides.
            if (!$isMethod && $name === 'array_map' && isset($args[1])
                && ($e->args[0]->value ?? null) instanceof Scalar\String_) {
                $cb = strtolower($e->args[0]->value->value);
                $src = $args[1];
                if (isset($SANFN[$cb])) {
                    // the callback receives the element as its FIRST argument, so a sanitizer whose value
                    // sits elsewhere (mysqli_real_escape_string takes the connection first) is not being
                    // used the way the catalog describes: that is an unknown call, not a substitution
                    if (($SANFN[$cb]['arg'] ?? 0) !== 0) return through($src, $cb . '()', $line, true);
                    return sanitize($src, $SANFN[$cb]['contexts'], 'array_map:' . $cb, $line);
                }
                if (isset($PRESERV[$cb])) return through($src, null, $line, false, 'all');
                if (isset($NARROW[$cb]))  return through($src, null, $line, false, 'numeric');
                if (isset($TRANSP[$cb]))  return through($src, null, $line, false, 'none');
            }
            // sanitizers: substitution of the value for the listed contexts
            $san = $isMethod ? $qual($SANMETH) : ($e instanceof Expr\StaticCall ? ($qual($SANMETH) ?? ($SANFN[$name] ?? null)) : ($SANFN[$name] ?? null));
            if ($san !== null) {
                $ix = $san['arg'] ?? 0; if ($ix < 0) $ix = count($args) - 1;
                $s = $args[$ix] ?? stF();
                $ctxs = $san['contexts'];
                if (!$isMethod && ($name === 'htmlspecialchars' || $name === 'htmlentities')) {
                    // the single quote is encoded only with ENT_QUOTES — the default since PHP 8.1; a flag argument is read
                    // for the constant names it names (classification only)
                    $flags = $e->args[1]->value ?? null;
                    $q = $flags === null
                        ? (($GLOBALS['phpVersion'] === null || version_compare($GLOBALS['phpVersion'], '8.1', '>=')) ? 'both' : 'double')
                        : self::entQuotes($flags);
                    if ($q === 'both') $ctxs = array_values(array_unique(array_merge($ctxs, ['html-sq'])));
                    // quote bits of zero: this encodes NEITHER quote, so it does not close a double-quoted
                    // attribute either — body text only. `null` means the flags could not be read: nothing is
                    // concluded from them and the catalog's contexts stand.
                    elseif ($q === 'none') $ctxs = array_values(array_map(fn($c) => $c === 'html' ? 'html-text' : $c, $ctxs));
                }
                return sanitize($s, $ctxs, ($isMethod ? ($recv ?? '->' . $name) : $name), $line);
            }
            // defined in THIS file: inline with the caller's argument states
            if (!$isMethod && $e instanceof Expr\FuncCall && isset($this->defs['fn'][$name]))
                return $this->inline($this->defs['fn'][$name], $args, $line, 'fn:' . $name);
            if ($isMethod && $e->var instanceof Expr\Variable && $e->var->name === 'this' && $this->currentClass !== null) {
                [$owner, $def] = $this->findMethod($this->currentClass, $name);
                if ($def !== null) return $this->inline($def, $args, $line, 'm:' . $owner . '::' . $name);
            }
            if ($e instanceof Expr\StaticCall && $e->class instanceof Node\Name && $this->currentClass !== null
                && in_array(strtolower($e->class->toString()), ['self', 'static', 'parent', strtolower($this->currentClass)], true)) {
                $start = strtolower($e->class->toString()) === 'parent' ? ($this->parents[$this->currentClass] ?? null) : $this->currentClass;
                if ($start !== null) {
                    [$owner, $def] = $this->findMethod($start, $name);
                    if ($def !== null) return $this->inline($def, $args, $line, 'm:' . $owner . '::' . $name);
                }
            }
            if ($fmt !== null) return $name === 'printf' ? stF() : $fmt;
            if (!$isMethod && $name === 'filter_var') {
                $flt = $e->args[1]->value ?? null;
                $fname = $flt instanceof Expr\ConstFetch ? strtoupper($flt->name->toString()) : '';
                if (in_array($fname, self::VALIDATE_FIXED, true))
                    return sanitize($args[0] ?? stF(), ['*'], 'filter_var:' . $fname, $line);
                if ($fname === 'FILTER_SANITIZE_SPECIAL_CHARS' || $fname === 'FILTER_SANITIZE_FULL_SPECIAL_CHARS')   // = htmlspecialchars, both quotes
                    return sanitize($args[0] ?? stF(), ['html', 'html-sq'], 'filter_var:' . $fname, $line);
                // FILTER_SANITIZE_EMAIL REMOVES, AND WHAT IT LEAVES IS THE POINT. MEASURED on PHP 8.3.6: a string
                // holding a double quote, a single quote, angle brackets, a slash, a backslash, a space and a
                // newline comes back without any of them EXCEPT the single quote, and "</script>" comes back
                // "script". So it substitutes in body text and in a double-quoted attribute, and nowhere that a
                // single quote closes something: not html-sq, not sql-quoted, not a single-quoted script string.
                if ($fname === 'FILTER_SANITIZE_EMAIL')
                    return sanitize($args[0] ?? stF(), ['html'], 'filter_var:' . $fname, $line);
                // FILTER_SANITIZE_URL is deliberately NOT here: measured, it strips the space and the newline and
                // leaves the quote, the angle bracket, the slash and the backslash exactly where they were.
                return through(joinAll($args ?: [stF()]), null, $line, false, 'none');
            }
            // preg_replace('/[^a-z0-9]/', '', $x): everything outside a plain class is REMOVED, so the result lives in
            // that class — a substitution by construction, the same credit as an anchored preg_match guard
            if (!$isMethod && $name === 'preg_replace' && ($e->args[0]->value ?? null) instanceof Scalar\String_
                && ($e->args[1]->value ?? null) instanceof Scalar\String_ && $e->args[1]->value->value === ''
                && self::patternStripsToClass($e->args[0]->value->value))
                return sanitize($args[2] ?? stF(), ['*'], 'preg_replace-strip', $line);
            // preg_replace('/"/', '', $x): the pattern's language is a SET OF SINGLE CHARACTERS and the
            // replacement is empty, so the result CANNOT CONTAIN any of them. That closes exactly the html
            // positions those characters close, and no other: `sq-closed` is not `html-sq`.
            if (!$isMethod && $name === 'preg_replace'
                && ($e->args[1]->value ?? null) instanceof Scalar\String_ && $e->args[1]->value->value === ''
                && ($cs = self::patternCharSet($e->args[0]->value ?? null)) !== null
                && ($cc = self::closedBy($cs)) !== [])
                return addSan($args[2] ?? stF(), $cc, 'preg_replace-removes', $line);
            if (!$isMethod && ($name === 'explode' || $name === 'implode' || $name === 'join')) {
                // Splitting/joining on a literal delimiter that carries no quote, backslash or NUL cannot
                // strand an escape: preserving. A delimiter WITH quotes is safe too when it has an EVEN
                // number of each — it closes one literal and opens the next, leaving the quoting state as
                // it found it. `implode("','", $escaped)` inside `'...'` is the canonical SQL IN-list, and
                // WordPress core builds get_page_by_path() that way (post.php: esc_sql($parts) then
                // implode("','", ...)); an ODD count stands a quote in the middle of one element and does
                // strand the escape. Measured 2026-09-10.
                $delim = $e->args[0]->value ?? null;
                $safe = $delim instanceof Scalar\String_ && !preg_match('/[\\\\\x00]/', $delim->value)
                    && substr_count($delim->value, "'") % 2 === 0 && substr_count($delim->value, '"') % 2 === 0;
                $data = $args[1] ?? $args[0] ?? stF();
                return through($data, null, $line, false, $safe ? 'all' : 'numeric');
            }
            // A SUMMARY OF THE CALLEE, learned in pass 1 from another file. Four things it can say, and
            // each is more precise than "unknown call": the result carries this argument's taint; the
            // result is opaque; the result is CLEAN of it (a real sanitizer, the case that used to cost
            // us thousands of false OPEN); and — the one that finds flaws — the argument reaches a SINK
            // inside, which is emitted here, in the caller's context, with the callee named.
            $sumKey = $isMethod ? null : ($SUMMARIES['functions'][$name] ?? null);
            // a method summary is read ONLY when the receiver's class is known to be the current one ($this->m(),
            // self::m(), static::m()) — `$db->safe()` inside class CUsers is not CUsers::safe (Fable's review of the
            // Opus pass, 2026-09-09: the lookup went by the CALLER's class for any receiver)
            $recvIsSelf = ($isMethod && $e->var instanceof Expr\Variable && $e->var->name === 'this')
                || ($e instanceof Expr\StaticCall && $e->class instanceof Node\Name && in_array(strtolower($e->class->toString()), ['self', 'static'], true));
            if ($sumKey === null && $recvIsSelf && $this->currentClass !== null) {
                // up the parent chain, as PHP resolves it: the definition that runs may live in a
                // class this file never mentions (SMF: UnreadReplies extends Unread, another file)
                $cls = strtolower($this->currentClass); $seenC = [];
                $own = [];                                    // the `extends` written in THIS file, by lowercase name
                foreach ($this->parents as $c => $pp) $own[strtolower($c)] = strtolower($pp);
                while ($cls !== null && !isset($seenC[$cls])) {
                    $seenC[$cls] = true;
                    if (isset($SUMMARIES['methods'][$cls . '::' . $name])) { $sumKey = $SUMMARIES['methods'][$cls . '::' . $name]; break; }
                    // a parent written here is not a guess about a name — it is this file's own text
                    $cls = $own[$cls] ?? ($SUMMARIES['parents'][$cls] ?? null);
                }
            }
            // A METHOD CALL ON A FOREIGN OBJECT. `$langs->trans($x)` — we do not know $langs's class, and a
            // method NAME is not an act. But if EVERY definition of that name in the tree agrees in substance,
            // which one runs cannot change the answer. The assumption this rests on, and the reason it is off
            // by default: the object may be a vendor's or PHP's own, whose definition is not in the tree.
            $assumedName = null;
            if ($sumKey === null && $ASSUME_TREE && $isMethod && !$recvIsSelf) {
                $sumKey = $SUMMARIES['byname'][$name] ?? null;
                if ($sumKey !== null && empty($sumKey['conflict'])) $assumedName = '->' . $name . '()';
            }
            if ($sumKey !== null && !empty($sumKey['conflict'])) $sumKey = null;          // two different definitions: unknown
            if ($sumKey !== null && !isset($this->defs['fn'][$name])) {
                $tainted = [];
                foreach ($args as $ix => $st) if (($st['t'] ?? 'F') !== 'F') $tainted[] = (string)$ix;
                foreach ($sumKey['sinks'] as [$k, $ctx]) {
                    $ix = ($k === 'any') ? null : (int)$k;
                    $st = $ix === null ? joinAll($args ?: [stF()]) : ($args[$ix] ?? null);
                    if ($st !== null && ($st['t'] ?? 'F') !== 'F')
                        $this->sinkFact($ctx, $name . '()→sink', $line, $st);
                }
                $carried = [];
                foreach ($tainted as $k) {
                    // "any": the parameters were probed all at once, so the answer is about ALL the arguments together,
                    // not about this one. Matching only the argument's own index dropped it, and request data passed
                    // through img_picto() or dol_escape_htmltag() read as "constants only" (xany, 2026-09-11). Carried
                    // as UNKNOWN: "some argument arrives raw" does not say THIS one does (dol_escape_htmltag's raw one
                    // is $noescapetags; accusing $_SERVER['PHP_SELF'] of it made 29 false alarms on dolibarr). The
                    // substitutions are kept: escaped with every argument tainted is escaped with any one of them,
                    // since the walk takes the same paths whatever is tainted.
                    if (!in_array($k, $sumKey['passes'], true) && in_array('any', $sumKey['passes'], true)) {
                        $st = $args[(int)$k];
                        $ctxs = $sumKey['substitutes']['any'] ?? [];
                        $carried[] = through($ctxs ? sanitize($st, $ctxs, $name . '()', $line) : $st, $name . '()', $line, true, 'all');
                    } elseif (in_array($k, $sumKey['passes'], true)) {
                        $st = $args[(int)$k];
                        $ctxs = $sumKey['substitutes'][$k] ?? [];
                        $carried[] = $ctxs ? sanitize($st, $ctxs, $name . '()', $line) : $st;
                    } elseif (in_array($k, $sumKey['opaque'], true) || in_array('any', $sumKey['opaque'], true)) {
                        $carried[] = through($args[(int)$k], $name . '()', $line, true);
                    }
                    // neither: the callee does not carry this argument into its result — nothing to add
                }
                $res = $carried ? joinAll($carried) : stF();
                // THE CALLEE'S OWN SOURCE (xown): request data the body produces by itself comes back whatever the arguments were.
                // ZERO-TRUST CHOICE (curator 2026-09-11): carry it as UNKNOWN, not an accusation. The summary is a single-path
                // approximation — "the body returns request data on SOME path" does not prove THIS call is exploitable, because a
                // helper like dolibarr's GETPOST($k, $filter) sanitizes or not depending on $filter, which the summary cannot read.
                // So the caller reads OPEN with the callee named, never REFUTED on the summary alone (measured: the accusing form
                // added 3205 false REFUTED across 48 CMS via getpost(); this form adds 0, and clears the same false "clean").
                $own = $sumKey['own'] ?? 'F';
                if ($own === 'T') { $o = stT('fn', $name . '()', $line); if (!empty($sumKey['own_san'])) $o = sanitize($o, $sumKey['own_san'], $name . '()', $line); $res = join2($res, through($o, 'own:' . $name . '()', $line, true, 'all')); }
                elseif ($own === 'Z') $res = join2($res, stZ('inside ' . $name . '()', $line));
                // THE ASSUMPTION TRAVELS WITH THE VALUE. When the answer came from the tree's definitions of
                // a bare method name, the receiver's class was never checked — so every verdict downstream
                // says so, in the ledger and in the summary, and nothing rests on it silently.
                if ($assumedName !== null) $res['as'] = uniq(array_merge($res['as'] ?? [], [[$assumedName, $line]]));
                return $res;
            }
            // str_replace('"', '', $x): the same claim, written the plainer way. Only SINGLE characters count —
            // removing a phrase (`str_replace('<!-- warning -->', '', $x)`) leaves every character of it behind.
            if (!$isMethod && ($name === 'str_replace' || $name === 'str_ireplace')
                && ($e->args[1]->value ?? null) instanceof Scalar\String_ && $e->args[1]->value->value === '') {
                $srch = $e->args[0]->value ?? null;
                $chars = null;
                if ($srch instanceof Scalar\String_ && strlen($srch->value) === 1) $chars = [$srch->value];
                elseif ($srch instanceof Expr\Array_) {
                    $chars = [];
                    foreach ($srch->items as $it) {
                        if ($it === null || !($it->value instanceof Scalar\String_) || strlen($it->value->value) !== 1) { $chars = null; break; }
                        $chars[] = $it->value->value;
                    }
                }
                if ($chars !== null && ($cc = self::closedBy($chars)) !== [])
                    return addSan($args[2] ?? stF(), $cc, 'str_replace-removes', $line);
            }
            if (!$isMethod && ($name === 'str_replace' || $name === 'str_ireplace' || $name === 'strtr') && self::replacementIsPlain($e, $name)) {
                // A LITERAL SEARCH/REPLACE DRAWN FROM [A-Za-z0-9_-,] CANNOT BREAK ANY SUBSTITUTION WE HOLD.
                // replacementIsPlain has already checked that every replacement lives in that alphabet, and no
                // context of ours treats a letter, digit, `_`, `-` or `,` as dangerous — so a value escaped for
                // html, for a quoted SQL string, for a header or for a path is still escaped afterwards. Removal
                // cannot create a dangerous character either: if the substitution holds, none is there to juxtapose.
                // Before this only `*` survived, and two real cases died on it: SMF's
                // `strtr(basename($x), ':/', '-_')` (Smileys.php:1530) and SuiteCRM's
                // `str_replace('+', '_', urlencode($name))` before a Content-Disposition header
                // (download.php:264 -> 295), 41 verdicts behind the second. Measured 2026-09-09.
                $data = $name === 'strtr' ? ($args[0] ?? stF()) : ($args[2] ?? stF());
                return through($data, null, $line, false, 'all');
            }
            if (!$isMethod && isset($PRESERV[$name])) return through(joinAll($args ?: [stF()]), null, $line, false, 'all');
            if (!$isMethod && isset($NARROW[$name]))  return through(joinAll($args ?: [stF()]), null, $line, false, 'numeric');
            // json_encode with the JSON_HEX_* flags is a JavaScript-string encoder: no quote, bracket or ampersand survives
            if (!$isMethod && $name === 'json_encode' && isset($e->args[1]) && self::mentionsConst($e->args[1]->value, 'JSON_HEX_TAG'))
                return sanitize($args[0] ?? stF(), ['js'], 'json_encode:JSON_HEX', $line);
            if (!$isMethod && isset($TRANSP[$name]))  return through(joinAll($args ?: [stF()]), null, $line, false, 'none');
            if (($isMethod || $e instanceof Expr\StaticCall) && $qual($TRANSPMETH) !== null) return through(joinAll($args ?: [stF()]), null, $line, false, 'none');   // a framework call declared transparent by an overlay
            if ($sinkCtx !== null) return stZ('db-or-sink-result', $line);   // a query's result is stored data: not visible here
            return through(joinAll($args ?: [stF()]), ($isMethod ? '->' : '') . $name . '()', $line, true);
        }
        if ($e instanceof Expr\List_) { return stZ('destructure', $line); }
        if ($e instanceof Expr\Exit_ || $e instanceof Expr\Throw_) { if ($e->expr) $this->ex($e->expr, $env); return stF(); }
        if ($e instanceof Expr\ErrorSuppress || $e instanceof Expr\Clone_ || $e instanceof Expr\PreInc || $e instanceof Expr\PreDec
            || $e instanceof Expr\PostInc || $e instanceof Expr\PostDec || $e instanceof Expr\BitwiseNot) {
            $s = $this->ex($e->expr ?? $e->var, $env); return $s;
        }
        if ($e instanceof Expr\ShellExec) {
            $st = []; foreach ($e->parts as $p) if ($p instanceof Expr) $st[] = $this->ex($p, $env);
            if (isset($SINKFN['shell_exec'])) $this->sinkFact($SINKFN['shell_exec'], '`backtick`', $line, joinAll($st ?: [stF()]));
            return $SRCSHELL ? stT('fn', '`backtick`', $line) : stZ('shell-result', $line);
        }
        // anything else: walk children conservatively
        $st = [];
        foreach ($e->getSubNodeNames() as $n) {
            $c = $e->$n;
            if ($c instanceof Expr) $st[] = $this->ex($c, $env);
            elseif (is_array($c)) foreach ($c as $cc) if ($cc instanceof Expr) $st[] = $this->ex($cc, $env);
        }
        return through(joinAll($st ?: [stF()]), 'node:' . $e->getType(), $line, true);
    }

    /** Is this a literal the machine may trust as a fixed set/value? (scalars, constants, arrays of them) */
    public static function isLiteral(?Node $n): bool {
        if ($n === null) return false;
        if ($n instanceof Scalar\String_ || $n instanceof Scalar\Int_ || $n instanceof Scalar\Float_ || $n instanceof Expr\ConstFetch || $n instanceof Expr\ClassConstFetch) return true;
        if ($n instanceof Expr\Array_) { foreach ($n->items as $it) { if ($it === null || !self::isLiteral($it->value)) return false; } return true; }
        return false;
    }

    /** An anchored pattern over a plain character class — the only regex we credit as a verification. */
    private static function patternIsTight(?Node $n): bool {
        $b = self::patternBody($n);
        return $b !== null && (bool)preg_match('/^(?:\^|\\\\A)' . self::ATOMS . '(?:\$|\\\\[zZ])$/', $b);
    }

    /** ANCHORS ARE A GUARD'S QUESTION, NOT A CAPTURE'S. `preg_match('~([A-Za-z0-9_-]+)~', $x, $m)` does not
     *  say the subject is confined — but $m holds only what the pattern matched, and that text is drawn
     *  from the pattern's own language. So for the matched text the question is just whether the body is
     *  characters we read: no `.`, no alternation, no backreference. Measured on SMF 2026-09-09
     *  (Languages.php:669), where the anchored test called a confined capture attacker-controlled. */
    private static function patternConfines(?Node $n): bool {
        $b = self::patternBody($n);
        if ($b === null) return false;
        $b = preg_replace('/^(?:\\^|\\\\A)/', '', $b);          // anchors are harmless here: they do not widen
        $b = preg_replace('/(?:\\$|\\\\[zZ])$/', '', $b);
        return $b !== '' && (bool)preg_match('/^' . self::ATOMS . '$/', $b);
    }

    private const ATOMS = '(?:(?:\[[A-Za-z0-9_\\\\\-]+\]|\\\\[dw]|[A-Za-z0-9_\-])(?:[+*?]|\{\d+(?:,\d*)?\})?)+';

    /** The body of a literal pattern, delimiters and flags removed, groups WITHOUT alternation flattened
     *  (a group adds nothing to the language). Null when the pattern is not a literal we can read, or
     *  carries the `m` flag, which makes `$` mean end-of-line rather than end-of-subject. */
    private static function patternBody(?Node $n): ?string {
        if (!($n instanceof Scalar\String_)) return null;
        $p = $n->value;
        if (strlen($p) < 3) return null;
        $d = $p[0]; $end = strrpos($p, $d);
        if ($end === false || $end === 0) return null;
        $flags = substr($p, $end + 1); $body = substr($p, 1, $end - 1);
        if (str_contains($flags, 'm')) return null;
        if (!str_contains($body, '|')) {
            for ($i = 0; $i < 8; $i++) {
                $next = preg_replace('/\((?:\?:)?([^()|]*)\)/', '$1', $body);
                if ($next === null || $next === $body) break;
                $body = $next;
            }
        }
        return $body;
    }

    /** THE CHARACTERS A LITERAL PATTERN CAN MATCH, when its language is a SET OF SINGLE CHARACTERS and
     *  nothing more: `/"/`, `/['"]/`, `/[<>]/`, with an optional `+` or `*`. Null for anything else — an
     *  anchor, an alternation, a multi-character sequence, a NEGATED class (that one is patternStripsToClass's
     *  business), a shorthand class like \\w whose membership we would have to enumerate. Removing such a set
     *  with an empty replacement means the result CANNOT CONTAIN any of them, and that is the whole claim. */
    private static function patternCharSet(?Node $n): ?array {
        $body = self::patternBody($n);
        if ($body === null || $body === '') return null;
        if (preg_match('/[+*?{}]$/', $body)) $body = rtrim($body, '+*');       // one or more of the same set
        if ($body === '' || str_contains($body, '|')) return null;
        if ($body[0] === '[') {
            if (substr($body, -1) !== ']' || strlen($body) < 3) return null;
            $inner = substr($body, 1, -1);
            if ($inner === '' || $inner[0] === '^' || str_contains($inner, '-')) return null;   // negated, or a range
            return self::literalChars($inner);
        }
        $c = self::literalChars($body);
        return ($c !== null && count($c) === 1) ? $c : null;
    }

    /** The characters of a class body, provided every one of them is a PLAIN character or a backslash
     *  escape of a punctuation character. `\\w`, `\\d`, `\\s` and their kin are refused: their membership
     *  is not on the page. */
    private static function literalChars(string $s): ?array {
        $out = [];
        for ($i = 0; $i < strlen($s); $i++) {
            $c = $s[$i];
            if ($c === '\\') {
                if ($i + 1 >= strlen($s)) return null;
                $n = $s[++$i];
                if (ctype_alnum($n)) return null;                              // \w \d \s \1 — not a character
                $out[] = $n;
                continue;
            }
            if (in_array($c, ['.', '(', ')', '[', ']', '{', '}', '*', '+', '?', '^', '$'], true)) return null;
            $out[] = $c;
        }
        return $out ?: null;
    }

    /** Which html position a removal closes. One closer per position, and NOTHING else follows from it:
     *  taking the single quote out settles a single-quoted attribute and says nothing about body text,
     *  where `<` still opens a tag. Measured 2026-09-10 on SARD CWE_79, where 21 files removing exactly
     *  one quote and landing in exactly that attribute came back REFUTED. */
    private static function closedBy(array $chars): array {
        $ctx = [];
        if (in_array("'", $chars, true)) $ctx[] = 'sq-closed';
        if (in_array('"', $chars, true)) $ctx[] = 'dq-closed';
        if (in_array('<', $chars, true)) $ctx[] = 'lt-closed';
        return $ctx;
    }

    /** What a condition VERIFIES: ['true' => [[var, contexts, fn, line]...], 'false' => [...]].
     *  A guard is an act of checking, and inside the branch it protects the value is substituted (E40:
     *  the sanitizer is a substitution, and a verified membership in a fixed set is one). */
    private function guards(Expr $c): array {
        global $GUARDS, $INERT;
        $line = $c->getStartLine();
        $none = ['true' => [], 'false' => []];
        // isset($a, $b, $c) IS isset($a) && isset($b) && isset($c) — PHP's own definition. Only the one-argument form was read,
        // so ErrorLog's `isset($_GET['value'], $_GET['filter'], $this->filters[$_GET['filter']])` was no check at all and the
        // filter name read as raw request data (f96, 2026-09-11). Rebuilt as the conjunction, it gets AND's rules exactly.
        if ($c instanceof Expr\Isset_ && count($c->vars) > 1) {
            $and = new Expr\Isset_([$c->vars[0]], $c->getAttributes());
            foreach (array_slice($c->vars, 1) as $iv) $and = new Expr\BinaryOp\BooleanAnd($and, new Expr\Isset_([$iv], $c->getAttributes()), $c->getAttributes());
            return $this->guards($and);
        }
        if ($c instanceof Expr\BooleanNot) { $g = $this->guards($c->expr); return ['true' => $g['false'], 'false' => $g['true'], 'unknown' => $g['unknown'] ?? [], 'unknown_false' => $g['unknown_true'] ?? [], 'unknown_true' => $g['unknown_false'] ?? []]; }
        if ($c instanceof Expr\BinaryOp\BooleanAnd || $c instanceof Expr\BinaryOp\LogicalAnd) {
            $l = $this->guards($c->left); $r = $this->guards($c->right);
            // `unknown_true` travels through AND — on the true branch BOTH sides held. It must NOT travel
            // through OR, where the true branch says only that one of them did. Without this,
            // `!empty($m) && isset($beanList[$m])` lost the membership credit and SuiteCRM's
            // TreeData.php:98 read as an unguarded include. Measured 2026-09-10.
            return ['true' => array_merge($l['true'], $r['true']), 'false' => [],
                    'unknown' => array_merge($l['unknown'] ?? [], $r['unknown'] ?? []),
                    'unknown_true' => array_merge($l['unknown_true'] ?? [], $r['unknown_true'] ?? [])];
        }
        if ($c instanceof Expr\BinaryOp\BooleanOr || $c instanceof Expr\BinaryOp\LogicalOr) {
            $l = $this->guards($c->left); $r = $this->guards($c->right);
            $both = [];                                                     // true only for a var BOTH sides verify
            foreach ($l['true'] as $a) foreach ($r['true'] as $b) if ($a[0] === $b[0]) $both[] = [$a[0], array_values(array_intersect($a[1], $b[1])) ?: (in_array('*', $a[1], true) ? $b[1] : (in_array('*', $b[1], true) ? $a[1] : [])), $a[2] . '|' . $b[2], $line];
            return ['true' => array_values(array_filter($both, fn($g) => $g[1] !== [])), 'false' => array_merge($l['false'], $r['false'])];
        }
        if ($c instanceof Expr\Cast\Bool_) return $this->guards($c->expr);
        if ($c instanceof Expr\BinaryOp\Identical || $c instanceof Expr\BinaryOp\Equal || $c instanceof Expr\BinaryOp\NotIdentical || $c instanceof Expr\BinaryOp\NotEqual
            || $c instanceof Expr\BinaryOp\Greater || $c instanceof Expr\BinaryOp\GreaterOrEqual || $c instanceof Expr\BinaryOp\Smaller || $c instanceof Expr\BinaryOp\SmallerOrEqual) {
            // `preg_match(...) == 1`, `=== true`, `!== false`, `> 0`: the comparison only reads the guard's own answer
            [$gx, $lit, $flip] = self::isLiteral($c->right) ? [$c->left, $c->right, false] : (self::isLiteral($c->left) ? [$c->right, $c->left, true] : [null, null, false]);
            if ($gx !== null && $this->guardName($gx) === null) {
                $truth = self::truthOf($lit); $sense = null;
                if ($c instanceof Expr\BinaryOp\Identical || $c instanceof Expr\BinaryOp\Equal) $sense = $truth;
                elseif ($c instanceof Expr\BinaryOp\NotIdentical || $c instanceof Expr\BinaryOp\NotEqual) $sense = $truth === null ? null : !$truth;
                elseif ($lit instanceof Scalar\Int_) {
                    $op = $c instanceof Expr\BinaryOp\Greater ? '>' : ($c instanceof Expr\BinaryOp\GreaterOrEqual ? '>=' : ($c instanceof Expr\BinaryOp\Smaller ? '<' : '<='));
                    if ($flip) $op = ['>' => '<', '>=' => '<=', '<' => '>', '<=' => '>='][$op];       // literal on the left: mirror
                    $n = $lit->value;
                    $sense = (($op === '>' && $n === 0) || ($op === '>=' && $n === 1)) ? true : (((($op === '<' && $n === 1) || ($op === '<=' && $n === 0))) ? false : null);
                }
                if ($sense !== null) { $g = $this->guards($gx); return $sense ? $g : ['true' => $g['false'], 'false' => $g['true']]; }
                return $none;
            }
        }
        if ($c instanceof Expr\BinaryOp\Identical || $c instanceof Expr\BinaryOp\Equal) {
            $v = $this->guardName($c->left) !== null && self::isLiteral($c->right) ? $this->guardName($c->left)
               : ($this->guardName($c->right) !== null && self::isLiteral($c->left) ? $this->guardName($c->right) : null);
            return $v === null ? $none : ['true' => [[$v, ['*'], 'equals-literal', $line]], 'false' => []];
        }
        if ($c instanceof Expr\BinaryOp\NotIdentical || $c instanceof Expr\BinaryOp\NotEqual) {
            $v = $this->guardName($c->left) !== null && self::isLiteral($c->right) ? $this->guardName($c->left)
               : ($this->guardName($c->right) !== null && self::isLiteral($c->left) ? $this->guardName($c->right) : null);
            return $v === null ? $none : ['true' => [], 'false' => [[$v, ['*'], 'equals-literal', $line]]];
        }
        if ($c instanceof Expr\Isset_ && count($c->vars) === 1 && $c->vars[0] instanceof Expr\ArrayDimFetch) {
            $adf = $c->vars[0];                                             // isset($FIXED[$x]) — membership in a fixed map
            // the KEY may be a request slot itself — `isset($map[$_GET['f']])` — named the way every other guard names it
            // (guardName: a variable OR an array slot). varName took plain variables only, so the commonest spelling of the
            // whitelist read as no check at all (f96, 2026-09-11).
            $v = ($adf->dim ?? null) !== null ? $this->guardName($adf->dim) : null;
            // `isset($map[$x])` where the map is FIXED: a constant, or a variable assigned a literal
            // array exactly once in the file. WordPress's _get_list_table gates `new $class_name` on
            // exactly this shape (`$core_classes` is a literal map, `isset($core_classes[$class_name])`),
            // and without the second case the whitelist read as no check at all. Measured 2026-09-09.
            if ($v !== null && ($adf->var instanceof Expr\ConstFetch || $adf->var instanceof Expr\ClassConstFetch
                                || ($adf->var instanceof Expr\Variable && $this->litOf($adf->var) instanceof Expr\Array_)))
                return ['true' => [[$v, ['*'], 'isset-fixed-map', $line]], 'false' => []];
            // A MAP WE CANNOT READ IS STILL A MAP. `isset($beanList[$module])` gates SuiteCRM's
            // `require_once('modules/'.$module.'/TreeData.php')` on a list built by an include —
            // a whitelist whose contents are invisible here, which is Z, not the absence of a check.
            // Its twin `array_key_exists($x, $map)` has answered exactly that since the guard work;
            // the two spellings of one act disagreed. Measured 2026-09-09 on SuiteCRM.
            // ON THE TRUE BRANCH ONLY. `isset($map[$x])` is the same act as array_key_exists, but it is
            // also PHP's universal "do I have this cached", and the NEGATIVE branch establishes nothing:
            // `if (!isset($cache[$id])) { $wpdb->get_var("... user_id=$id ..."); }` is not a checked value.
            // Applying it before the split cost four real catches on user-role-editor's own
            // "SQL-injection vulnerability fix" commits. Measured 2026-09-09.
            if ($v !== null) return ['true' => [], 'false' => [], 'unknown_true' => [[$v, 'isset(map)', $line]]];
            return $none;
        }
        if ($c instanceof Expr\FuncCall && $c->name instanceof Node\Name) {
            $fn = strtolower($c->name->toString());
            $args = $c->args;
            if ($fn === 'filter_var') {                                        // if (filter_var($x, FILTER_VALIDATE_INT)) — an act of checking
                $flt = $args[1]->value ?? null;
                $fname = $flt instanceof Expr\ConstFetch ? strtoupper($flt->name->toString()) : '';
                $v = isset($args[0]) ? $this->guardName($args[0]->value) : null;
                return ($v !== null && in_array($fname, self::VALIDATE_FIXED, true)) ? ['true' => [[$v, ['*'], 'guard:filter_var:' . $fname, $line]], 'false' => []] : $none;
            }
            $g = $GUARDS[$fn] ?? null;
            // READ, AND FOUND WANTING. file_exists() answers whether a path is on disk — not whether it is
            // one the developer named here; is_string() forbids no quote. These are not unknown checks: we
            // read them, they confine nothing, so they are no guard at all and the verdict stands.
            if ($g === null && isset($INERT[$fn])) return $none;
            if ($g === null) {
                // AN UNKNOWN CHECK IS NOT THE ABSENCE OF A CHECK. `if (!wp_check_jsonp_callback($cb)) return;`
                // reads the value and decides on it; we cannot see what it accepts. Calling that REFUTED accuses
                // someone else's code of a hole we never read — the move ZTL exists to refuse. The value becomes
                // Z with the checker named, so the verdict is OPEN and says whose check to go and read.
                // MEASURED 2026-09-09: 20 REFUTED on WordPress and phpMyAdmin, every one of this shape.
                foreach ($args as $arg) {
                    if (!($arg instanceof Node\Arg)) continue;
                    $v = $this->guardName($arg->value);
                    if ($v !== null) return ['true' => [], 'false' => [], 'unknown' => [[$v, $fn . '()', $line]]];
                }
                return $none;
            }
            $vix = $g['value'] ?? 0;
            $v = isset($args[$vix]) ? $this->guardName($args[$vix]->value) : null;
            if ($v === null) return $none;
            // A CHECK WE CANNOT READ IS STILL A CHECK. `array_key_exists($func, $actions)` where the
            // map comes back from a call is not "no whitelist" — it is a whitelist whose contents we
            // cannot see, and the honest answer is Z, not a refutation. Measured 2026-09-09 on
            // Wordfence 9.0.1 (wordfenceClass.php:1732), the single REFUTED across six live plugins.
            if (isset($g['haystack']) && $this->litOf($args[$g['haystack']]->value ?? null) === null)
                return ['true' => [], 'false' => [], 'unknown' => [[$v, $fn . '()', $line]]];
            // REJECT-IF-CONTAINS. `if (preg_match('/[^a-z0-9]/', $x)) { die(); }` is hand-rolled validation
            // written the other way round: the pattern matches everything OUTSIDE a readable class, so on the
            // path where it did NOT match, the value is confined to that class. The credit therefore belongs to
            // the FALSE branch — the mirror of pattern_tight, which credits the true one. A pattern that is not
            // a negated class (`/bad/`) confines nothing and gets nothing. Measured 2026-09-10.
            if (!empty($g['pattern_tight']) && ($pt = $this->litOf($args[$g['pattern']]->value ?? null)) instanceof Scalar\String_
                && self::patternStripsToClass($pt->value))
                return ['true' => [], 'false' => [[$v, ['*'], 'preg_match:rejects-outside-class', $line]]];
            if (!empty($g['pattern_tight'])) {
                $pat = $this->litOf($args[$g['pattern']]->value ?? null);
                // READ AND FOUND WANTING is not the same as UNREADABLE. `/[a-z]+/` is a pattern we
                // read and refuse to credit — it confines nothing — and the verdict stands. A pattern
                // we cannot read at all is an unknown check, and the honest answer there is Z.
                if ($pat === null) return ['true' => [], 'false' => [], 'unknown' => [[$v, $fn . '()', $line]]];
                if (!self::patternIsTight($pat)) return $none;
            }
            return ['true' => [[$v, $g['contexts'], 'guard:' . $fn, $line]], 'false' => []];
        }
        if (($c instanceof Expr\MethodCall || $c instanceof Expr\StaticCall || $c instanceof Expr\NullsafeMethodCall)
            && $c->name instanceof Node\Identifier) {                       // $this->isValid($x), $db->check($x): same rule
            $mname = strtolower($c->name->toString());
            foreach ($c->args as $arg) {
                if (!($arg instanceof Node\Arg)) continue;
                $v = $this->guardName($arg->value);
                if ($v !== null) return ['true' => [], 'false' => [], 'unknown' => [[$v, '->' . $mname . '()', $line]]];
            }
            return $none;
        }
        if ($c instanceof Expr\Assign) return $this->guards($c->expr);   // if ($m = preg_match(...)) — rare; keep simple
        return $none;
    }

    /** A value read by a check this file cannot see is UNVERIFIED — not clean, not refuted. */
    private function applyUnknownGuards(array $gs, array &$env): void {
        foreach ($gs as [$v, $fn, $line]) {
            // A REQUEST SLOT NOT READ HERE YET — `$_GET['f']` under `isset($this->filters[$_GET['f']])`. It is carried the way a
            // known guard's slot is (guardedSlots: scoped to this branch, met across branches), with the context '?': checked by
            // something we cannot read, so a later read is Z, not "read in full". Skipping it left SMF ErrorLog's whitelisted
            // filter name REFUTED (f96, 2026-09-11). A known guard already on the slot is stronger and stays.
            if (!isset($env[$v]) && str_contains($v, '[') && !isset($this->guardedSlots[$v])) { $this->guardedSlots[$v] = [['?'], $fn, $line]; continue; }
            if (!isset($env[$v]) || $env[$v]['t'] === 'F') continue;
            $env[$v] = through($env[$v], 'guarded-by:' . $fn, $line, true, 'all');
        }
    }

    private function applyGuards(array $gs, array &$env): void {
        foreach ($gs as [$v, $ctxs, $fn, $line])
            if (!isset($env[$v]) && str_contains($v, '[')) $this->guardedSlots[$v] = [$ctxs, $fn, $line];
        foreach ($gs as [$v, $ctxs, $fn, $line]) {
            if (!isset($env[$v]) && ($p = strpos($v, '[')) !== false && isset($env[substr($v, 0, $p)]))
                $env[$v] = $env[substr($v, 0, $p)];                 // an element slot not written here yet ($octet[0] after explode): the whole array's state
            if (!isset($env[$v])) continue;
            $x = $env[$v];
            $env[$v] = sanitize($x, $ctxs, $fn, $line);
            // a value DERIVED from $v before the check ($path = $dir . $ext; if (ctype_alpha($ext)) unlink($path)) is checked
            // too — but only when every tainted parent of it leads back to $v and nowhere else
            foreach ($env as $k => $y) {
                if ($k === $v || $y['t'] !== 'T') continue;
                if (self::derivesOnlyFrom($y, $v, $x, $env, [$k])) $env[$k] = sanitize($y, $ctxs, $fn . '-derived', $line);
            }
        }
    }

    /** Does every tainted parent of $y lead back to $x (and to no other attacker-controlled origin)? The sources of $y
     *  must be among $x's own, and each tainted parent must be $x or derive only from $x itself. A parent that is not
     *  in the env any more, or a cycle, is NOT credited. */
    private static function derivesOnlyFrom(array $y, string $xn, array $x, array $env, array $seen): bool {
        foreach ($y['src'] as $srow) if (!in_array($srow, $x['src'], true)) return false;
        $parents = $y['dv'] ?? [];
        if (!$parents) return false;
        foreach ($parents as $p) {
            if ($p === $xn) continue;
            if ($p === '#src') return false;                                  // read a source directly: its mark did not come through $x
            if (!isset($env[$p]) || in_array($p, $seen, true)) return false;
            $ps = $env[$p];
            if ($ps['t'] !== 'T') continue;                                  // a constant or opaque parent carries no attacker mark
            if (!self::derivesOnlyFrom($ps, $xn, $x, $env, array_merge($seen, [$p]))) return false;
        }
        return true;
    }

    /** The name a guard verifies: a plain variable, an element with a literal key (`$octet[0]`), or either of those seen
     *  through a PRESERVING function (`strtolower($ext) == 'jpg'` checks $ext — case changes cannot hide a quote). */
    private function guardName(?Node $n): ?string {
        global $PRESERV;
        if ($n instanceof Expr\Variable) return $this->varName($n);
        if ($n instanceof Expr\ArrayDimFetch) return self::slot($n);
        if ($n instanceof Expr\FuncCall && $n->name instanceof Node\Name && isset($PRESERV[strtolower($n->name->toString())]) && count($n->args) >= 1 && $n->args[0] instanceof Node\Arg)
            return $this->guardName($n->args[0]->value);
        return null;
    }

    /** Does a block always leave (return / exit / throw / break / continue)? Then what follows the `if`
     *  runs only when its condition FAILED, and the failed side's guards hold there. */
    private static function terminates(array $stmts): bool {
        if (!$stmts) return false;
        $last = $stmts[count($stmts) - 1];
        if ($last instanceof Stmt\Return_ || $last instanceof Stmt\Break_ || $last instanceof Stmt\Continue_) return true;
        if ($last instanceof Stmt\Expression && ($last->expr instanceof Expr\Exit_ || $last->expr instanceof Expr\Throw_)) return true;
        return false;
    }

    private function assignTo(Expr $target, array $rhs, array &$env, int $line, ?Node $rhsExpr = null): void {
        if ($target instanceof Expr\Variable) {
            $n = $this->varName($target);
            if ($n !== null) { $env[$n] = $rhs; foreach (array_keys($env) as $k) if (str_starts_with($k, $n . '[')) unset($env[$k]); }   // a fresh array: its old slots are gone
            else $this->ex($target, $env);
            return;
        }
        if ($target instanceof Expr\ArrayDimFetch && ($ps0 = self::propArraySlot($target)) !== null
            && $target->var instanceof Expr\PropertyFetch && $this->currentClass !== null) {
            $this->ex($target->dim, $env);
            // WRITING ONE KEY DOES NOT TAINT THE OTHERS. `$this->config['base_url'] = <from $_SERVER>`
            // used to be joined into the whole property, so `$this->config['theme']` — written nowhere
            // near it — read as attacker-controlled. Pico: all 9 of its refutations, measured 2026-09-09.
            // The element goes to its own slot; the whole-property read collects the slots (see ex()).
            $this->props[$this->currentClass][$ps0] = $rhs;
            return;
        }
        if ($target instanceof Expr\ArrayDimFetch && $target->var instanceof Expr\PropertyFetch
            && $target->var->var instanceof Expr\Variable && $target->var->var->name === 'this'
            && $target->var->name instanceof Node\Identifier && $this->currentClass !== null) {
            $this->ex($target->dim, $env);                        // a COMPUTED key: which element it is, we do not know,
            $pn = $target->var->name->toString();                 // so the whole property carries it. Previously dropped.
            $cur = $this->props[$this->currentClass][$pn] ?? stF();
            $this->props[$this->currentClass][$pn] = join2($cur, $rhs);
            // ...and into every element slot of it: the computed key may BE that element (f97, 2026-09-11)
            foreach (array_keys($this->props[$this->currentClass]) as $k)
                if (str_starts_with($k, $pn . '[')) $this->props[$this->currentClass][$k] = join2($this->props[$this->currentClass][$k], $rhs);
            return;
        }
        if ($target instanceof Expr\ArrayDimFetch) {
            $this->ex($target->dim, $env);
            $sk = self::slot($target);
            if ($sk !== null && $target->var instanceof Expr\Variable && isset($GLOBALS['SUPER'][$target->var->name])) {
                $env[$sk] = $rhs;                       // the slot now holds what was written into it
                return;
            }
            $root = $target; while ($root instanceof Expr\ArrayDimFetch) $root = $root->var;
            $n = $this->varName($root);
            if ($n !== null) {
                $sl = self::slot($target);
                // WRITING ONE KEY DOES NOT TAINT THE OTHERS — the same rule properties got today.
                // `$GLOBALS['a'] = $_GET['x']` used to be joined into the whole array, so `$GLOBALS['b']`,
                // written nowhere near it, read as attacker-controlled. A COMPUTED key still taints the
                // whole array, because which element it was is exactly what we do not know, and reading
                // the array AS A WHOLE joins the slots back in (envWhole). Measured 2026-09-09.
                if ($sl !== null) { $env[$sl] = $rhs; return; }
                $env[$n] = join2($env[$n] ?? stF(), $rhs);
                // A COMPUTED KEY MAY BE ANY KEY — also one that has its own slot. `$row['a'] = 'c'; $row[$_GET['k']] = $_GET['v']`
                // leaves $row['a'] attacker-controlled when k is 'a'; the slot kept 'c' and read EARNED, "constants only" (f97).
                foreach (array_keys($env) as $k) if (str_starts_with($k, $n . '[')) $env[$k] = join2($env[$k], $rhs);
            }
            return;
        }
        if ($target instanceof Expr\List_ || $target instanceof Expr\Array_) {
            foreach ($target->items as $it) { if ($it && $it->value instanceof Expr) $this->assignTo($it->value, through($rhs, null, $line, false, 'all'), $env, $line); }
            return;
        }
        if ($target instanceof Expr\PropertyFetch && $target->var instanceof Expr\Variable && $target->var->name === 'this'
            && $target->name instanceof Node\Identifier && $this->currentClass !== null) {
            $pn = $target->name->toString();
            // `$this->p = <expr built only from $this->p and literals>` ADDS NOTHING. Pico writes
            // `$this->config = is_array($this->config) ? $this->config : array();` — with properties held as
            // a class-wide join with no order between methods, that read-back carried a tainted element
            // written in another method back into the bulk, and every other key inherited it. All 9 of
            // Pico's refutations, measured 2026-09-09.
            if ($this->selfOnly($rhsExpr ?? null, $pn)) return;
            $cur = $this->props[$this->currentClass][$pn] ?? null;
            $this->props[$this->currentClass][$pn] = ($cur === null || $this->instanceMode) ? $rhs : join2($cur, $rhs);   // a concrete instance: strong update
            foreach (array_keys($this->props[$this->currentClass]) as $k) if (str_starts_with($k, $pn . '[')) unset($this->props[$this->currentClass][$k]);   // a fresh array clears its old element slots
            return;
        }
        // other objects' properties, static properties: not tracked
    }

    /** Analyse a callee body with the caller's argument states; sinks inside are emitted in the caller's
     *  context, the joined `return` state comes back. Depth-capped and recursion-cut: past the cap the call
     *  is what it was before — unknown. */
    /** Run a method of an in-file class on ONE object's property states: the class-wide map is swapped for the
     *  instance's for the duration of the call and the instance keeps what the method left behind. */
    private function instanceCall(array &$inst, string $method, array $args, int $line): array {
        $cn = $inst['class']; $def = $this->defs['m'][$cn][$method];
        $key = 'm:' . $cn . '::' . $method;
        if ($this->pass === 1) $this->callers[$key] = ($this->callers[$key] ?? 0) + 1;   // seen in pass 1, read when the class is walked in pass 2
        $saveClass = $this->currentClass; $saveProps = $this->props[$cn] ?? null; $saveMode = $this->instanceMode;
        $this->currentClass = $cn; $this->props[$cn] = $inst['props']; $this->instanceMode = true;
        $r = $this->inline($def, $args, $line, $key);
        $inst['props'] = $this->props[$cn];
        if ($saveProps === null) unset($this->props[$cn]); else $this->props[$cn] = $saveProps;
        $this->currentClass = $saveClass; $this->instanceMode = $saveMode;
        return $r;
    }

    public bool $returnedBool = false;

    /** Set the class context for a summary probe (methods read $this->prop). */
    public function currentClassPublic(?string $cls): void { $this->currentClass = $cls; }
    /** The superglobal slots this walk vouched for, for the file-level summary of a front controller. */
    public function guardedSlotsPublic(): array { return $this->guardedSlots; }
    /** A guard an INCLUDED file put on this slot, carried in before the walk. */
    public function seedGuardedSlot(string $slot, array $ctxs, string $fn, int $line): void {
        $this->guardedSlots[$slot] = [$ctxs, $fn, $line];
    }

    public static function isLiteralPublic(?Node $n): bool { return self::isLiteral($n); }

    /** Walk a definition's body with the given parameter states and return the joined `return`. */
    public function probeBody(array $stmts, array $env): array {
        $this->returns[] = [];
        $this->walk($stmts, $env);
        $rets = array_pop($this->returns);
        foreach ($rets as $r) if (($r['t'] ?? 'F') === 'F') { $this->returnedBool = true; break; }
        return $rets ? joinAll($rets) : stF();
    }

    /** Record one unknown check: on a plain variable, on a superglobal element with a literal key, or
     *  on what a value was BUILT FROM when that is readable — `$m = array($_SERVER['PHP_SELF']);
     *  their_gate($m);` checks the slot, and a copy of a PHP string or array carries the same value.
     *  Only through a name written exactly once, and only one hop deep. */
    public function noteUnknownCheck(?Node $arg, string $who, array $once = [], int $depth = 0): void {
        $v = $arg instanceof Node\Arg ? $arg->value : $arg;
        if (!($v instanceof Expr)) return;                        // `foo(...)` hands us a VariadicPlaceholder, not an expression
        if ($v instanceof Expr\Variable && is_string($v->name)) {
            $this->unknownChecked[$v->name] = $who;
            if ($depth < 1 && isset($once[$v->name])) $this->noteUnknownCheck($once[$v->name], $who, $once, $depth + 1);
            return;
        }
        if ($v instanceof Expr\Array_) {
            foreach ($v->items as $it) if ($it !== null) $this->noteUnknownCheck($it->value, $who, $once, $depth);
            return;
        }
        $sl = self::slot($v);
        if ($sl !== null) $this->unknownCheckedSlots[$sl] = $who;
    }

    /** Is every leaf of this expression either `$this-><pn>` itself or a literal? Then assigning it back
     *  to `$this-><pn>` cannot introduce anything the property did not already carry. */
    private function selfOnly(?Node $e, string $pn): bool {
        if ($e === null) return false;
        $ok = true;
        $walk = function (?Node $n) use (&$walk, &$ok, $pn) {
            if ($n === null || !$ok) return;
            if ($n instanceof Expr\PropertyFetch && $n->var instanceof Expr\Variable && $n->var->name === 'this'
                && $n->name instanceof Node\Identifier && $n->name->toString() === $pn) return;
            if ($n instanceof Scalar\String_ || $n instanceof Scalar\Int_ || $n instanceof Scalar\Float_
                || $n instanceof Expr\ConstFetch || $n instanceof Expr\ClassConstFetch || $n instanceof Scalar\MagicConst) return;
            if ($n instanceof Expr\Array_) { foreach ($n->items as $it) { if ($it) { $walk($it->key); $walk($it->value); } } return; }
            if ($n instanceof Expr\Ternary) { $walk($n->cond); $walk($n->if); $walk($n->else); return; }
            if ($n instanceof Expr\BinaryOp) { $walk($n->left); $walk($n->right); return; }
            if ($n instanceof Expr\BooleanNot || $n instanceof Expr\Empty_) { $walk($n->expr); return; }
            if ($n instanceof Expr\FuncCall && $n->name instanceof Node\Name
                && in_array(strtolower($n->name->toString()), ['is_array', 'is_string', 'isset', 'empty', 'count'], true)) {
                foreach ($n->args as $a) if ($a instanceof Node\Arg) $walk($a->value);
                return;
            }
            $ok = false;
        };
        $walk($e);
        return $ok;
    }

    /** THE WHOLE ARRAY: what was written to the name in bulk, joined with every element slot written
     *  under it. Reading `$arr` must still see `$arr['k']`; only reading a DIFFERENT literal key must
     *  not. Null when nothing at all is known about the name. */
    private static function envWhole(array $env, string $n): ?array {
        $parts = [];
        if (isset($env[$n])) $parts[] = $env[$n];
        $pfx = $n . '[';
        foreach ($env as $k => $st) if (is_string($k) && str_starts_with($k, $pfx)) $parts[] = $st;
        return $parts ? joinAll($parts) : null;
    }

    /** THE WHOLE PROPERTY: what was written to it in bulk, joined with every element slot. Reading
     *  `$this->config` must still see `$this->config['base_url']`; only reading a DIFFERENT literal
     *  key must not. Null when nothing at all is known about the name. */
    private function propWhole(string $cls, string $pn): ?array {
        $parts = [];
        if (isset($this->props[$cls][$pn])) $parts[] = $this->props[$cls][$pn];
        foreach ($this->props[$cls] ?? [] as $k => $st) if (str_starts_with($k, $pn . '[')) $parts[] = $st;
        return $parts ? joinAll($parts) : null;
    }

    /** The definition a `$this->m()` call actually runs: this class, else up the parent chain. */
    private function findMethod(?string $cls, string $name): array {
        $seen = [];
        while ($cls !== null && !isset($seen[$cls])) {
            $seen[$cls] = true;
            if (isset($this->defs['m'][$cls][$name])) return [$cls, $this->defs['m'][$cls][$name]];
            $cls = $this->parents[$cls] ?? null;
        }
        return [null, null];
    }

    private function inline(Node $def, array $args, int $line, string $key): array {
        if (count($this->callStack) >= $this->callDepth || in_array($key, $this->callStack, true))
            return through(joinAll($args ?: [stF()]), 'call-depth:' . $key, $line, true);
        if ($this->inlineSpent >= $this->inlineBudget)
            return through(joinAll($args ?: [stF()]), 'call-budget:' . $key, $line, true);
        $this->inlineSpent++;
        $env = [];
        foreach ($def->params as $i => $p) {
            $n = $this->varName($p->var); if ($n === null) continue;
            if ($p->variadic) { $env[$n] = joinAll(array_slice($args, $i) ?: [stF()]); break; }
            $env[$n] = $args[$i] ?? ($p->default !== null ? $this->ex($p->default, $env) : stF());
        }
        $saveScope = $this->scope; $this->scope = $saveScope . '→' . $key . '@L' . $line;
        $this->callStack[] = $key; $this->returns[] = [];
        if ($def->stmts !== null) $this->walk($def->stmts, $env);
        $rets = array_pop($this->returns); array_pop($this->callStack);
        $this->scope = $saveScope;
        return $rets ? joinAll($rets) : stF();
    }

    /** The html stream state after paths rejoin: the same on every path, or unknown. */
    private static function hsJoin(array $hss): array {
        $k = Html::key($hss[0]);
        foreach ($hss as $h) if (Html::key($h) !== $k) return Html::unknown();
        return $hss[0];
    }

    /** Guarded slots after a join: a slot survives only if EVERY path guarded it, and then only for the contexts
     *  every path covered (`*` covers all). Different wording of the same guard keeps the first path's name. */
    private static function gsMeet(array $gss): array {
        $out = array_shift($gss);
        foreach ($gss as $m) {
            foreach ($out as $slot => [$ctxs, $fn, $ln]) {
                if (!isset($m[$slot])) { unset($out[$slot]); continue; }
                $o = $m[$slot][0];
                $c = $ctxs === ['*'] ? $o : ($o === ['*'] ? $ctxs : array_values(array_intersect($ctxs, $o)));
                if (!$c) unset($out[$slot]); else $out[$slot] = [$c, $fn, $ln];
            }
        }
        return $out;
    }

    /** Pairwise fold of joinEnv — same result, no cross-product over many paths. */
    private static function joinFold(array $envs, array $pre): array {
        $acc = array_shift($envs);
        foreach ($envs as $e) $acc = self::joinEnv([$acc, $e], $pre);
        return $acc;
    }

    private static function joinEnv(array $envs, array $pre): array {
        $names = [];
        foreach ($envs as $e) foreach ($e as $k => $_) $names[$k] = 1;
        $out = [];
        foreach (array_keys($names) as $k) {
            $st = []; $arr = ($p = strpos($k, '[')) !== false ? substr($k, 0, $p) : null;
            foreach ($envs as $e) $st[] = $e[$k] ?? ($pre[$k] ?? ($arr !== null ? ($e[$arr] ?? $pre[$arr] ?? stZ('maybe-unassigned:$' . $arr . '[…]', 0)) : stZ('maybe-unassigned:$' . $k, 0)));
            // THE SAME STATE ON EVERY SIDE IS ITS OWN JOIN. Most names are untouched by a branch, and their states are the very
            // same array on both sides — PHP answers === for that by pointer. Joining them anyway allocated a fresh copy, broke the
            // sharing, and every later join paid in full: tcpdf.php spent 25 of 27 s of one probe here (2026-09-11).
            $same = true; foreach ($st as $i => $x) if ($i > 0 && $x !== $st[0]) { $same = false; break; }
            $out[$k] = $same ? $st[0] : joinAll($st);
        }
        return $out;
    }
    private static function envEq(array $a, array $b): bool {
        if (count($a) !== count($b)) return false;                 // cheap gate before the expensive test
        foreach ($a as $k => $v) { if (!array_key_exists($k, $b) || $v !== $b[$k]) return false; }
        return true;                                                // PHP compares arrays structurally
    }

    public function walk(array $stmts, array &$env): void {
        foreach ($stmts as $s) $this->stmt($s, $env);
    }

    private function stmt(Node $s, array &$env): void {
        if (++$this->nodeSpent > $this->nodeBudget) return;
        global $SINKFLAGS;
        $line = $s->getStartLine();
        if ($s instanceof Stmt\Expression) { $this->ex($s->expr, $env); return; }
        if ($s instanceof Stmt\Echo_) {
            foreach ($s->exprs as $x) { $st = $this->ex($x, $env); if (isset($SINKFLAGS['echo'])) $this->output('echo', $line, $st); else self::htmlEmbed($this->hs, $st, $_n); }
            return;
        }
        if ($s instanceof Stmt\InlineHTML) { $this->hs = Html::advance($this->hs, $s->value); return; }
        if ($s instanceof Stmt\Return_) { $st = $s->expr ? $this->ex($s->expr, $env) : stF(); if ($this->returns) $this->returns[count($this->returns) - 1][] = $st; return; }
        if ($s instanceof Stmt\If_) {
            $this->ex($s->cond, $env);
            $g = $this->guards($s->cond);
            // An unknown check is applied to the env BEFORE the split, so the mark survives the join.
            // Its meaning is not "checked on this path" but "this file contains code that reads this
            // value and decides on it, and I cannot read what it accepts" — which is true on every
            // path, including the one where the condition was false. Measured 2026-09-09: without
            // this, a guard nested one level (`if ($cb) { if (!check($cb)) return; }`, the WordPress
            // REST shape) was lost at the join and the verdict went back to REFUTED.
            $this->applyUnknownGuards($g['unknown'] ?? [], $env);
            $paths = []; $hs0 = $this->hs; $hss = [];
            // guarded slots, like the env, belong to a PATH (f90): each branch starts from $gs0 and the join
            // keeps a slot only if every path that goes on guarded it — a path that exits drops out, so
            // `if ($x != 'a') exit;` still guards what follows.
            $gs0 = $this->guardedSlots; $gss = [];
            $e1 = $env; $this->applyGuards($g['true'], $e1);
            $this->applyUnknownGuards($g['unknown_true'] ?? [], $e1);   // membership: only the branch where it HOLDS
            $this->walk($s->stmts, $e1);
            $leaves = self::terminates($s->stmts);
            if (!$leaves) { $paths[] = $e1; $hss[] = $this->hs; $gss[] = $this->guardedSlots; }
            foreach ($s->elseifs as $ei) { $this->hs = $hs0; $this->guardedSlots = $gs0; $e2 = $env; $this->applyGuards($g['false'], $e2); $this->ex($ei->cond, $e2); $this->applyGuards($this->guards($ei->cond)['true'], $e2); $this->walk($ei->stmts, $e2); if (!self::terminates($ei->stmts)) { $paths[] = $e2; $hss[] = $this->hs; $gss[] = $this->guardedSlots; } }
            if ($s->else) { $this->hs = $hs0; $this->guardedSlots = $gs0; $e3 = $env; $this->applyGuards($g['false'], $e3); $this->applyUnknownGuards($g['unknown_false'] ?? [], $e3); $this->walk($s->else->stmts, $e3); if (!self::terminates($s->else->stmts)) { $paths[] = $e3; $hss[] = $this->hs; $gss[] = $this->guardedSlots; } }
            else { $this->guardedSlots = $gs0; $e0 = $env; $this->applyGuards($g['false'], $e0); $this->applyUnknownGuards($g['unknown_false'] ?? [], $e0); $paths[] = $e0; $hss[] = $hs0; $gss[] = $this->guardedSlots; }   // the fall-through path: the condition failed
            $env = $paths ? self::joinFold($paths, $env) : $env;
            $this->hs = self::hsJoin($hss ?: [$hs0]);
            $this->guardedSlots = $gss ? self::gsMeet($gss) : $gs0;
            return;
        }
        if ($s instanceof Stmt\While_ || $s instanceof Stmt\Do_ || $s instanceof Stmt\For_ || $s instanceof Stmt\Foreach_) {
            if ($s instanceof Stmt\For_) { foreach ($s->init as $x) $this->ex($x, $env); }
            $acc = $env;
            for ($i = 0; $i < $this->loopCap; $i++) {
                $body = $acc;
                if ($s instanceof Stmt\Foreach_) {
                    $it = $this->ex($s->expr, $body);
                    if ($s->keyVar) $this->assignTo($s->keyVar, through($it, null, $line, false, 'all'), $body, $line);
                    $this->assignTo($s->valueVar, through($it, null, $line, false, 'all'), $body, $line);
                } elseif ($s instanceof Stmt\While_) { $this->ex($s->cond, $body); }
                elseif ($s instanceof Stmt\For_) { foreach ($s->cond as $x) $this->ex($x, $body); }
                $this->walk($s->stmts, $body);
                if ($s instanceof Stmt\For_) { foreach ($s->loop as $x) $this->ex($x, $body); }
                if ($s instanceof Stmt\Do_) { $this->ex($s->cond, $body); }
                $next = self::joinEnv([$acc, $body], $acc);
                if (self::envEq($next, $acc)) { $acc = $next; break; }
                $acc = $next;
                if ($i === $this->loopCap - 1) { foreach ($acc as $k => $v) { if (!self::envEq($v, $body[$k] ?? [])) { $acc[$k]['t'] = ($acc[$k]['t'] === 'F') ? 'Z' : $acc[$k]['t']; $acc[$k]['z'][] = ['loop-not-converged', $line]; } } }
            }
            $env = $acc;
            return;
        }
        if ($s instanceof Stmt\Switch_) {
            $this->ex($s->cond, $env);
            $paths = []; $prev = null; $hasDefault = false;
            $subj = $this->guardName($s->cond);
            $hs0 = $this->hs; $hss = [];
            foreach ($s->cases as $c) {
                if ($c->cond === null) $hasDefault = true; else $this->ex($c->cond, $env);
                $e1 = $prev === null ? $env : self::joinEnv([$env, $prev], $env);
                if ($subj !== null && $c->cond !== null && self::isLiteral($c->cond) && isset($e1[$subj])) $e1[$subj] = sanitize($e1[$subj], ['*'], 'case-literal', $c->getStartLine());
                $this->hs = $hs0; $this->walk($c->stmts, $e1); $hss[] = $this->hs;
                $paths[] = $e1; $prev = $e1;
            }
            if (!$hasDefault) { $paths[] = $env; $hss[] = $hs0; }
            // Accumulate instead of holding every path: a `switch` with 350 cases over 191 variables
            // (WordPress `module.audio-video.quicktime.php`) made the final joinEnv walk the whole
            // cross-product and the file took 297 s alone. Join is associative, so folding pairwise
            // gives the same environment. MEASURED 2026-09-09.
            $env = self::joinFold($paths ?: [$env], $env);
            $this->hs = self::hsJoin($hss ?: [$hs0]);
            return;
        }
        if ($s instanceof Stmt\TryCatch) {
            $e1 = $env; $this->walk($s->stmts, $e1);
            $paths = [$e1];
            foreach ($s->catches as $c) { $e2 = self::joinEnv([$env, $e1], $env); if ($c->var) $this->assignTo($c->var, stZ('exception', $line), $e2, $line); $this->walk($c->stmts, $e2); $paths[] = $e2; }
            $env = self::joinEnv($paths, $env);
            if ($s->finally) $this->walk($s->finally->stmts, $env);
            return;
        }
        if ($s instanceof Stmt\Function_ || $s instanceof Stmt\ClassMethod) {
            // EACH TOP-LEVEL UNIT ITS OWN BUDGET (curator's idea, 2026-09-11): a big file is many units glued together — the
            // cross-file walk never starves because each file is its own unit with its own budget, joined by summaries. So a
            // 400-method class is analysed like 400 includes: reset the node budget per top-level method/function, and the
            // global inline cap (inlineSpent) still bounds total inlining, so later methods fall back to summaries, not a walk
            // that never ends. Only at the true top level (never inside an inlined body, which enters via walk(), not here).
            if (empty($this->callStack)) $this->nodeSpent = 0;
            $inner = [];
            foreach ($s->params as $p) { $n = $this->varName($p->var); if ($n !== null) $inner[$n] = stZ('param:$' . $n, $line); }
            $save = $this->scope; $this->scope = ($s instanceof Stmt\ClassMethod ? $save . '::' : '') . $s->name->toString() . '()';
            $key = $s instanceof Stmt\ClassMethod ? 'm:' . ($this->currentClass ?? '?') . '::' . strtolower($s->name->toString()) : 'fn:' . strtolower($s->name->toString());
            $this->functions[] = ['scope' => $this->scope, 'callers' => $this->callers[$key] ?? 0];
            $this->returns[] = [];
            $hs0 = $this->hs; $this->hs = Html::unknown();                     // a standalone body: its output lands who knows where
            if ($s->stmts !== null) $this->walk($s->stmts, $inner);
            $this->hs = $hs0;
            array_pop($this->returns);
            $this->scope = $save;
            return;
        }
        if ($s instanceof Stmt\Class_ || $s instanceof Stmt\Trait_ || $s instanceof Stmt\Interface_ || $s instanceof Stmt\Enum_) {
            $save = $this->scope; $this->scope = ($s->name ? $s->name->toString() : 'anon-class');
            $saveClass = $this->currentClass; $this->currentClass = $this->scope;
            foreach ($s->stmts as $m) { if ($m instanceof Stmt\ClassMethod) $this->stmt($m, $env); }
            $this->currentClass = $saveClass;
            $this->scope = $save;
            return;
        }
        if ($s instanceof Stmt\Global_) { foreach ($s->vars as $v) { $n = $this->varName($v); if ($n !== null) $env[$n] = stZ('global:$' . $n, $line); } return; }
        if ($s instanceof Stmt\Static_) { foreach ($s->vars as $v) { $n = $this->varName($v->var); if ($n !== null) $env[$n] = stZ('static:$' . $n, $line); } return; }
        if ($s instanceof Stmt\Unset_) { foreach ($s->vars as $v) { $n = $this->varName($v); if ($n !== null) unset($env[$n]); $sl = self::slot($v); if ($sl !== null) unset($env[$sl]); } return; }
        if ($s instanceof Stmt\Block || $s instanceof Stmt\Namespace_ || $s instanceof Stmt\Declare_) { if (!empty($s->stmts)) $this->walk($s->stmts, $env); return; }
        if ($s instanceof Stmt\Nop || $s instanceof Stmt\Use_ || $s instanceof Stmt\Const_
            || $s instanceof Stmt\Break_ || $s instanceof Stmt\Continue_ || $s instanceof Stmt\Goto_ || $s instanceof Stmt\Label
            || $s instanceof Stmt\HaltCompiler || $s instanceof Stmt\GroupUse) return;
        // unknown statement kind: evaluate any expressions it holds
        foreach ($s->getSubNodeNames() as $n) { $c = $s->$n; if ($c instanceof Expr) $this->ex($c, $env); elseif (is_array($c)) foreach ($c as $cc) { if ($cc instanceof Expr) $this->ex($cc, $env); elseif ($cc instanceof Stmt) $this->stmt($cc, $env); } }
    }
}

// --------------------------------------------------------------------- run
$parser = $phpVersion ? (new ParserFactory)->createForVersion(\PhpParser\PhpVersion::fromString($phpVersion))
                      : (new ParserFactory)->createForNewestSupportedVersion();
$out = ['tool' => 'code2zfl/atoms.php', 'php' => $phpVersion ?: 'newest', 'catalog' => basename($catalogPath), 'overlays' => array_map('basename', $overlays), 'files' => []];
foreach ($files as $f) {
    $rec = ['file' => $f, 'parse_error' => null, 'lines' => 0, 'sinks' => [], 'includes' => [], 'functions' => []];
    $code = @file_get_contents($f);
    if ($code === false) { $rec['parse_error'] = 'unreadable'; $out['files'][] = $rec; continue; }
    $rec['lines'] = substr_count($code, "\n") + 1;
    try {
        $ast = $parser->parse($code);
    } catch (ParseError $e) {
        $rec['parse_error'] = 'line ' . $e->getStartLine() . ': ' . preg_replace('/ on line \d+$/', '', $e->getRawMessage());
        $out['files'][] = $rec; continue;
    }
    $an = new Analyzer($CAT);
    $finder = new \PhpParser\NodeFinder;
    foreach ($finder->findInstanceOf($ast ?? [], Stmt\Function_::class) as $fn) $an->defs['fn'][strtolower($fn->name->toString())] = $fn;
    foreach ($finder->findInstanceOf($ast ?? [], Stmt\Class_::class) as $cls) {
        $cn = $cls->name ? $cls->name->toString() : 'anon-class';
        if ($cls->extends instanceof Node\Name) $an->parents[$cn] = $cls->extends->getLast();
        foreach ($cls->stmts as $m) if ($m instanceof Stmt\ClassMethod) $an->defs['m'][$cn][strtolower($m->name->toString())] = $m;
        foreach ($finder->findInstanceOf($cls, Expr\MethodCall::class) as $mc)
            if ($mc->var instanceof Expr\Variable && $mc->var->name === 'this' && $mc->name instanceof Node\Identifier) {
                $k = 'm:' . $cn . '::' . strtolower($mc->name->toString()); $an->callers[$k] = ($an->callers[$k] ?? 0) + 1;
            }
        foreach ($finder->findInstanceOf($cls, Expr\StaticCall::class) as $sc)
            if ($sc->class instanceof Node\Name && in_array(strtolower($sc->class->toString()), ['self', 'static', strtolower($cn)], true) && $sc->name instanceof Node\Identifier) {
                $k = 'm:' . $cn . '::' . strtolower($sc->name->toString()); $an->callers[$k] = ($an->callers[$k] ?? 0) + 1;
            }
    }
    foreach ($finder->findInstanceOf($ast ?? [], Expr\FuncCall::class) as $fc)
        if ($fc->name instanceof Node\Name && isset($an->defs['fn'][strtolower($fc->name->toString())])) {
            $k = 'fn:' . strtolower($fc->name->toString()); $an->callers[$k] = ($an->callers[$k] ?? 0) + 1;
        }
    // variables assigned EXACTLY ONCE in the whole file, from a literal: a guard may read them as that literal
    // (`$re = "/^[0-9]+$/"; if (preg_match($re, $x))`). Any other write — a second assignment, a compound one, a
    // parameter, a foreach, a global/static, a closure use, a list() — disqualifies the name. By-reference
    // arguments are not tracked: a list handed to a function that fills it would still read as fixed (boundary).
    $writes = [];
    $w = function ($v) use (&$writes) { if ($v instanceof Expr\Variable && is_string($v->name)) $writes[$v->name][] = null; };
    foreach ($finder->findInstanceOf($ast ?? [], Expr\Assign::class) as $as) {
        if ($as->var instanceof Expr\Variable && is_string($as->var->name)) $writes[$as->var->name][] = $as->expr;
        elseif ($as->var instanceof Expr\List_ || $as->var instanceof Expr\Array_) foreach ($as->var->items as $it) if ($it) $w($it->value);
        else { $root = $as->var; while ($root instanceof Expr\ArrayDimFetch) $root = $root->var; $w($root); }
    }
    foreach ($finder->find($ast ?? [], fn($n) => $n instanceof Expr\AssignOp || $n instanceof Expr\AssignRef || $n instanceof Expr\PreInc || $n instanceof Expr\PreDec || $n instanceof Expr\PostInc || $n instanceof Expr\PostDec) as $n) $w($n->var);
    foreach ($finder->findInstanceOf($ast ?? [], Node\Param::class) as $p) $w($p->var);
    foreach ($finder->findInstanceOf($ast ?? [], Stmt\Foreach_::class) as $fe) { $w($fe->keyVar); $w($fe->valueVar); }
    foreach ($finder->findInstanceOf($ast ?? [], Stmt\Global_::class) as $g) foreach ($g->vars as $v) $w($v);
    foreach ($finder->findInstanceOf($ast ?? [], Stmt\Static_::class) as $g) foreach ($g->vars as $v) $w($v->var);
    foreach ($finder->findInstanceOf($ast ?? [], Stmt\Catch_::class) as $c) $w($c->var);
    foreach ($finder->findInstanceOf($ast ?? [], Node\ClosureUse::class) as $u) $w($u->var);
    foreach ($finder->findInstanceOf($ast ?? [], Stmt\Unset_::class) as $u) foreach ($u->vars as $v) $w($v);
    foreach ($writes as $vn => $rhs) if (count($rhs) === 1 && $rhs[0] !== null && Analyzer::isLiteral($rhs[0])) $an->lits[$vn] = $rhs[0];
    // pass 1 collects property assignments (reads see Z); pass 2 reads them and is the one reported
    // PRE-PASS for unknown checks: any condition that hands a plain variable to a call we do not
    // know. Conditions only — an unknown call in ordinary code is already handled as an opaque value.
    prePassUnknownChecks($an, $ast ?? [], $finder);
    $endsHere = $ENDS;                                            // plus what THIS file defines
    foreach ($finder->findInstanceOf($ast ?? [], Stmt\Function_::class) as $fnDef)
        if (bodyEnds($fnDef->stmts)) $endsHere[strtolower($fnDef->name->toString())] = 1;
    foreach ($finder->findInstanceOf($ast ?? [], Stmt\ClassMethod::class) as $mDef)
        if (bodyEnds($mDef->stmts)) $endsHere[strtolower($mDef->name->toString())] = 1;
    $onceHere = [];
    foreach ($writes as $vn => $rhs) if (count($rhs) === 1 && $rhs[0] !== null) $onceHere[$vn] = $rhs[0];
    prePassTerminatingCalls($an, $ast ?? [], $finder, $endsHere, $onceHere);
    // WHAT THIS FILE INHERITS FROM WHAT IT INCLUDES (pass 1 built the graph, the driver closed it).
    // A page that requires a front controller is judged under the front controller's guards.
    $inh = $SUMMARIES['inherit'][@realpath($f) ?: $f] ?? $SUMMARIES['inherit'][$f] ?? null;
    if ($inh !== null) {
        foreach ($inh['unk'] ?? [] as $slot => $who) $an->unknownCheckedSlots[$slot] = $who;
        foreach ($inh['grd'] ?? [] as [$slot, $ctxs, $gn, $gl]) $an->seedGuardedSlot($slot, $ctxs, $gn . '@include', $gl);
        foreach ($inh['set'] ?? [] as $slot) $an->unknownCheckedSlots[$slot] = 'written-by-an-include';
    }
    $env = [];
    $an->pass = 1; $an->walk($ast ?? [], $env);
    $an->facts = []; $an->includes = []; $an->functions = []; $an->hs = Html::init('text');
    $env = [];
    $an->pass = 2; $an->walk($ast ?? [], $env);
    // a loop body is walked more than once (fixed point): one sink call site, one fact — states JOINED
    $byKey = [];
    foreach ($an->facts as $f) {
        $k = $f['ctx'] . '|' . $f['fn'] . '|' . $f['line'] . '|' . $f['scope'];
        if (!isset($byKey[$k])) { $byKey[$k] = $f; continue; }
        $j = join2($byKey[$k], $f);
        foreach (['t', 'src', 'san', 'z', 'q', 'zu', 'nu'] as $c) $byKey[$k][$c] = $j[$c];
        if (($f['hctx'] ?? null) !== null) $byKey[$k]['hctx'] = Html::worse($byKey[$k]['hctx'] ?? null, $f['hctx']);
    }
    // A CLASS DEFINED TWICE IN THE TREE: ONLY ONE COPY RUNS, AND THIS FILE'S TEXT DOES NOT SAY WHICH.
    // The verdicts here stand for the code as written; whether this code is the code that executes is a
    // separate question, and the ledger must not be silent about it. Measured 2026-09-10: 40 of 779 REFUTED
    // across five corpora sit in such a file, among them zurmo's `eval($_GET)` — whose live core holds no
    // eval at all, the second copy of the framework does.
    $dups = [];
    $nss2 = $finder->findInstanceOf($ast ?? [], Stmt\Namespace_::class);
    $ns2 = (count($nss2) === 1 && $nss2[0]->name !== null) ? strtolower($nss2[0]->name->toString()) : (count($nss2) === 0 ? '' : null);
    if ($ns2 !== null && !empty($SUMMARIES['classfiles'])) {
        foreach ($finder->findInstanceOf($ast ?? [], Stmt\Class_::class) as $cls2) {
            if (!$cls2->name) continue;
            $fq2 = $ns2 . '\\' . strtolower($cls2->name->toString());
            $where = $SUMMARIES['classfiles'][$fq2] ?? [];
            if (count($where) > 1) $dups[] = ['class' => $fq2, 'files' => count($where)];
        }
    }
    if ($dups) $rec['dup_classes'] = $dups;
    $rec['sinks'] = array_values($byKey); $rec['includes'] = array_values(array_unique($an->includes)); $rec['functions'] = $an->functions;
    if ($an->inlineSpent >= 3000) $rec['inline_budget_exhausted'] = true;   // named, not hidden
    if ($an->nodeSpent > 120000) $rec['node_budget_exhausted'] = true;      // the walk was cut short
    $out['files'][] = $rec;
}
/** PRE-PASS for unknown checks: any CONDITION that hands a value to a call we do not know.
 *  Conditions only — an unknown call in ordinary code is already handled as an opaque value. */
function prePassUnknownChecks(Analyzer $an, $ast, \PhpParser\NodeFinder $finder): void {
    global $GUARDS, $SANFN, $SANMETH, $PRESERV, $NARROW, $TRANSP, $SINKFN, $SINKMETH;
    // a TERNARY's condition checks its value exactly as an `if` does, and PHP writes validate-or-default
    // that way more often than not — so it belongs in this pre-pass with the statement forms.
    $conds = [];
    foreach (['If_', 'ElseIf_', 'While_', 'Do_'] as $kind) {
        foreach ($finder->findInstanceOf($ast, 'PhpParser\\Node\\Stmt\\' . $kind) as $node)
            if (($node->cond ?? null) !== null) $conds[] = $node->cond;
    }
    foreach ($finder->findInstanceOf($ast, Expr\Ternary::class) as $node) $conds[] = $node->cond;
    foreach ($conds as $cond) {
            foreach ($finder->findInstanceOf($cond, Expr\FuncCall::class) as $call) {
                $nm = $call->name instanceof Node\Name ? strtolower($call->name->toString()) : null;
                // "unknown" means absent from EVERY table we have — a name we know as preserving,
                // narrowing, transparent, a sanitizer or a sink is not a mystery checker. Without this
                // `if (strtolower($ext) == 'jpg')` counted as an unreadable check (fixtures f46/f47).
                if ($nm === null || isset($GUARDS[$nm]) || $nm === 'filter_var' || isset($SANFN[$nm])
                    || isset($PRESERV[$nm]) || isset($NARROW[$nm]) || isset($TRANSP[$nm]) || isset($SINKFN[$nm])
                    || function_exists($nm)) continue;
                foreach ($call->args as $arg) $an->noteUnknownCheck($arg, $nm . '()');
            }
            foreach ($finder->findInstanceOf($cond, Expr\MethodCall::class) as $call) {
                if (!($call->name instanceof Node\Identifier)) continue;
                $nm = strtolower($call->name->toString());
                if (isset($SANMETH[$nm]) || isset($SINKMETH[$nm])) continue;
                foreach ($call->args as $arg) $an->noteUnknownCheck($arg, '->' . $nm . '()');
            }
    }
}

/** Can this definition REFUSE THE REQUEST? A body that can `exit`, `die` or `throw` is a body that may
 *  end the run — and a call to it, standing as a statement, is an act of checking whatever it was given.
 *  Nested closures and definitions do not count: their exit belongs to a call that may never happen. */
function bodyEnds(?array $stmts): bool {
    if ($stmts === null) return false;
    foreach ($stmts as $st) {
        if ($st instanceof Stmt\Function_ || $st instanceof Stmt\ClassLike) continue;
        $f = new \PhpParser\NodeFinder;
        foreach ($f->find([$st], fn($n) => $n instanceof Expr\Exit_ || $n instanceof Stmt\Throw_ || $n instanceof Expr\Throw_) as $hit) {
            return true;
        }
    }
    return false;
}

/** A STATEMENT CALL TO SOMETHING THAT CAN REFUSE is a check. `analyseVarsForSqlAndScriptsInjection($v, 2);`
 *  stands alone on its line and dies on bad input — dolibarr's whole WAF is shaped this way. Reading it as
 *  an ordinary call left every page after it looking unprotected: 3258 accusations, measured 2026-09-09. */
function prePassTerminatingCalls(Analyzer $an, $ast, \PhpParser\NodeFinder $finder, array $ends, array $once): void {
    foreach ($finder->findInstanceOf($ast, Stmt\Expression::class) as $stmt) {
        $c = $stmt->expr;
        $nm = null;
        if ($c instanceof Expr\FuncCall && $c->name instanceof Node\Name) $nm = strtolower($c->name->toString());
        elseif (($c instanceof Expr\MethodCall || $c instanceof Expr\StaticCall) && $c->name instanceof Node\Identifier) $nm = strtolower($c->name->toString());
        if ($nm === null || !isset($ends[$nm])) continue;
        $who = ($c instanceof Expr\FuncCall ? $nm : '->' . $nm) . '()';
        foreach ($c->args as $arg) $an->noteUnknownCheck($arg, $who, $once);
    }
}

/** THE STATEMENTS THAT RUN WHEN THE FILE IS INCLUDED — everything except the bodies of definitions.
 *  A front controller's work sits here: the guards it puts on the request, and the files it pulls in. */
function topLevelStmts(array $stmts, array &$out): void {
    foreach ($stmts as $st) {
        if ($st instanceof Stmt\Function_ || $st instanceof Stmt\ClassLike) continue;
        $out[] = $st;
        foreach (['stmts', 'else', 'elseifs', 'catches', 'finally', 'cases'] as $slot) {
            $sub = $st->$slot ?? null;
            if (is_array($sub)) {
                $onlyStmts = array_values(array_filter($sub, fn($x) => $x instanceof Node\Stmt));
                $nested = array_values(array_filter($sub, fn($x) => !($x instanceof Node\Stmt)));
                if ($onlyStmts) topLevelStmts($onlyStmts, $out);
                foreach ($nested as $n) if (isset($n->stmts) && is_array($n->stmts)) topLevelStmts($n->stmts, $out);
            } elseif ($sub instanceof Node\Stmt) {
                topLevelStmts([$sub], $out);
            }
        }
    }
}

/** The LITERAL TAIL of an include path we could not resolve: `SOMECONST . '/a/b.php'` gives '/a/b.php'.
 *  Only a tail that starts with a separator and names a php file is worth handing on — anything shorter
 *  matches too much, and a tail is only ever accepted by the driver when exactly one scanned file ends
 *  with it. Null when the last part is not a literal. */
function includeTail(?Node $e): ?string {
    while ($e instanceof Expr\BinaryOp\Concat) $e = $e->right;
    if (!($e instanceof Scalar\String_)) return null;
    $v = $e->value;
    if (!str_starts_with($v, '/') || strlen($v) < 8 || !str_ends_with(strtolower($v), '.php')) return null;
    return $v;
}

/** The file an `include`/`require` names, when we can read it. A literal path, `__DIR__ . '/x.php'`,
 *  `dirname(__FILE__) . '/x.php'`. Anything built from a constant we cannot see (DOL_DOCUMENT_ROOT)
 *  comes back null — and that is a NAMED boundary in the ledger, not a silence. */
function resolveInclude(?Node $e, string $fromFile): ?string {
    $dir = dirname($fromFile);
    $cand = null;
    if ($e instanceof Scalar\String_) {
        $cand = str_starts_with($e->value, '/') ? $e->value : $dir . '/' . $e->value;
    } elseif ($e instanceof Expr\BinaryOp\Concat) {
        $l = $e->left; $r = $e->right;
        $isDir = ($l instanceof Scalar\MagicConst\Dir)
              || ($l instanceof Expr\FuncCall && $l->name instanceof Node\Name
                  && strtolower($l->name->toString()) === 'dirname'
                  && (($l->args[0]->value ?? null) instanceof Scalar\MagicConst\File));
        if ($isDir && $r instanceof Scalar\String_) $cand = $dir . '/' . ltrim($r->value, '/');
    }
    if ($cand === null) return null;
    $rp = @realpath($cand);
    return ($rp !== false && is_file($rp)) ? $rp : null;
}

/** Two summaries for one name: identical in substance → keep; otherwise a conflict. */
function summaryMerge(?array $a, array $b): array {
    if ($a === null) return $b;
    if (!empty($a['conflict'])) return $a;
    $strip = fn(array $r) => array_diff_key($r, ['file' => 1, 'line' => 1]);
    if ($strip($a) == $strip($b)) return $a;
    return ['conflict' => true, 'files' => array_values(array_unique(array_merge($a['files'] ?? [$a['file']], [$b['file']])))];
}

if ($emitSummaries) {
    // PASS 1. What does each definition DO with an attacker-controlled parameter? Walk its body once
    // per parameter (up to 4; beyond that mark them together and say so), and read the result off the
    // machinery that already exists: the returned state, and the sinks the walk emitted.
    $sum = ['tool' => 'code2zfl/atoms.php --emit-summaries', 'functions' => [], 'methods' => [], 'files' => [], 'parents' => [], 'classfiles' => []];
    foreach ($files as $f) {
        $code = @file_get_contents($f); if ($code === false) continue;
        try { $ast = $parser->parse($code); } catch (ParseError $e) { continue; }
        $finder = new \PhpParser\NodeFinder;
        $defs = [];
        foreach ($finder->findInstanceOf($ast ?? [], Stmt\Function_::class) as $fn)
            $defs[] = ['fn', strtolower($fn->name->toString()), $fn, null];
        // WHICH NAMESPACE THIS FILE IS IN — needed to say WHICH class a name means. Read from the AST, not
        // guessed: a file may hold several namespace blocks, and then no single answer is right, so we take
        // one only when there is exactly one.
        $nss = $finder->findInstanceOf($ast ?? [], Stmt\Namespace_::class);
        $fileNs = (count($nss) === 1 && $nss[0]->name !== null) ? strtolower($nss[0]->name->toString()) : (count($nss) === 0 ? '' : null);
        foreach ($finder->findInstanceOf($ast ?? [], Stmt\Class_::class) as $cls) {
            $cn = $cls->name ? $cls->name->toString() : 'anon-class';
            // WHERE ELSE THIS CLASS IS DEFINED. One name in two files means only one of them runs, and which
            // one is not in this file's text: an accusation inside the other copy points at code that may be
            // dead. Measured 2026-09-10: zurmo keeps a whole second copy of its framework
            // (extensions/zurmoinc, 483 files) whose Controller holds an `eval` the live core does not.
            if ($cls->name && $fileNs !== null) {
                $fq = $fileNs . '\\' . strtolower($cn);
                $sum['classfiles'][$fq] = array_values(array_unique(array_merge($sum['classfiles'][$fq] ?? [], [$f])));
            }
            if ($cls->extends instanceof Node\Name) {
                // THE CHAIN PHP WILL FOLLOW — but this map is keyed by the BARE class name, and one name can
                // belong to two namespaces (phpspreadsheet: Reader\Csv extends BaseReader, Writer\Csv extends
                // BaseWriter). Last-writer-wins made the answer depend on which BATCH a file landed in: measured
                // 2026-09-10 on dolibarr, 13 of 1725 names got a different parent at --jobs 12 and --jobs 16.
                // One name, two answers is a CONFLICT, and a guess is worse than a gap.
                $k = strtolower($cn); $pn = strtolower($cls->extends->getLast());
                $sum['parents'][$k] = (array_key_exists($k, $sum['parents']) && $sum['parents'][$k] !== $pn) ? null : $pn;
            }
            foreach ($cls->stmts as $m) if ($m instanceof Stmt\ClassMethod)
                $defs[] = ['m', strtolower($m->name->toString()), $m, $cn];
        }
        // The once-assigned literals of THIS file, collected the same way pass 2 collects them.
        // Without this the summary pass could not read a whitelist held in a variable, and
        // WordPress's _get_list_table (a literal $core_classes map) summarised as an open callable.
        $litWrites = [];
        $wf = function ($v, $rhs = null) use (&$litWrites) {
            if ($v instanceof Expr\Variable && is_string($v->name)) $litWrites[$v->name][] = $rhs;
        };
        foreach ($finder->findInstanceOf($ast ?? [], Expr\Assign::class) as $as) $wf($as->var, $as->expr);
        foreach ($finder->find($ast ?? [], fn($n) => $n instanceof Expr\AssignOp || $n instanceof Expr\AssignRef) as $as) $wf($as->var ?? null, null);
        foreach ($finder->findInstanceOf($ast ?? [], Node\Param::class) as $p) $wf($p->var, null);
        foreach ($finder->findInstanceOf($ast ?? [], Stmt\Foreach_::class) as $fe) { $wf($fe->keyVar, null); $wf($fe->valueVar, null); }
        foreach ($finder->findInstanceOf($ast ?? [], Stmt\Global_::class) as $g) foreach ($g->vars as $v) $wf($v, null);

        // WHAT THE FILE DOES WHEN IT IS INCLUDED. A front controller guards the request and pulls in
        // more files; every page then inherits both. Without this an `include` was a blind spot the
        // size of the whole architecture: measured 2026-09-09, dolibarr's WAF (htdocs/waf.inc.php,
        // reached through main.inc.php from every page) was invisible and produced 3258 accusations.
        $top = []; topLevelStmts($ast ?? [], $top);
        $frec = ['inc' => [], 'tail' => [], 'unresolved' => 0, 'unk' => [], 'grd' => [], 'set' => [], 'entry_blocked' => false];
        // CAN THIS FILE BE REQUESTED DIRECTLY? A template that names a constant it never defines —
        // dolibarr's tpl files open with `require_once DOL_DOCUMENT_ROOT.'/...'` — cannot run standalone:
        // on a direct request the constant is undefined and PHP stops before anything below. That is what
        // makes it safe to give the file what its includers guarantee. A file with no such marker may be
        // reachable on its own, and inherits nothing. `defined()` in OUR process answers exactly the
        // question "is this a PHP built-in", which is the half we must not mistake for a project constant.
        $ownConst = [];
        foreach ($finder->findInstanceOf($ast ?? [], Expr\FuncCall::class) as $dc)
            if ($dc->name instanceof Node\Name && strtolower($dc->name->toString()) === 'define'
                && ($dc->args[0]->value ?? null) instanceof Scalar\String_) $ownConst[$dc->args[0]->value->value] = 1;
        foreach ($finder->findInstanceOf($ast ?? [], Stmt\Const_::class) as $cs)
            foreach ($cs->consts as $cc) $ownConst[$cc->name->toString()] = 1;
        // ORDER DECIDES. A page defines the constants by requiring the front controller FIRST, and only
        // then uses them; a template uses one before it has required anything — often inside the require
        // itself. So walk the top level in order and stop at whichever comes first.
        foreach ($top as $st0) {
            $undef = false;
            foreach ($finder->findInstanceOf([$st0], Expr\ConstFetch::class) as $cf) {
                $cn = $cf->name->toString();
                if (isset($ownConst[$cn]) || defined($cn) || in_array(strtolower($cn), ['true', 'false', 'null'], true)) continue;
                $undef = true; break;
            }
            if ($undef) { $frec['entry_blocked'] = true; break; }
            if ($finder->findInstanceOf([$st0], Expr\Include_::class)) break;   // the front controller ran: constants exist now
        }
        foreach ($finder->findInstanceOf($top, Expr\Include_::class) as $incNode) {
            $t = resolveInclude($incNode->expr, $f);
            if ($t !== null) { $frec['inc'][] = $t; continue; }
            // A PATH BUILT ON A CONSTANT WE CANNOT SEE still ends in a literal we CAN:
            // `DOL_DOCUMENT_ROOT.'/core/tpl/objectline_view.tpl.php'`. The tail alone does not name a
            // file — but the driver knows every file it was asked to scan, and a tail matching exactly
            // ONE of them is that one. Measured 2026-09-10: dolibarr resolves 3 includes per file and
            // leaves 17074 unresolved, so its templates had no includers at all and nothing to inherit.
            $tail = includeTail($incNode->expr);
            if ($tail !== null) $frec['tail'][] = $tail; else $frec['unresolved']++;
        }
        $frec['inc'] = array_values(array_unique($frec['inc']));
        if (!empty($frec['tail'])) $frec['tail'] = array_values(array_unique($frec['tail']));
        $endsLocal = [];                                              // definitions in THIS file that can refuse
        foreach ($finder->findInstanceOf($ast ?? [], Stmt\Function_::class) as $fnDef)
            if (bodyEnds($fnDef->stmts)) $endsLocal[strtolower($fnDef->name->toString())] = 1;
        foreach ($finder->findInstanceOf($ast ?? [], Stmt\ClassMethod::class) as $mDef)
            if (bodyEnds($mDef->stmts)) $endsLocal[strtolower($mDef->name->toString())] = 1;
        $onceTop = [];
        foreach ($litWrites as $vn => $rhs) if (count($rhs) === 1 && $rhs[0] !== null) $onceTop[$vn] = $rhs[0];
        $ta = new Analyzer($CAT);
        prePassUnknownChecks($ta, $top, $finder);
        prePassTerminatingCalls($ta, $top, $finder, $endsLocal, $onceTop);
        $tenv = [];
        try { $ta->probeBody($top, $tenv); } catch (\Throwable $e) { /* a file-level walk is best effort */ }
        $frec['unk'] = $ta->unknownCheckedSlots;
        foreach ($ta->guardedSlotsPublic() as $slot => [$ctxs, $gn, $gl]) $frec['grd'][] = [$slot, $ctxs, $gn, $gl];
        foreach ($tenv as $k => $v) if (str_contains($k, '[') && isset($SUPER[explode('[', $k)[0]])) $frec['set'][] = $k;
        $fkey = @realpath($f) ?: $f;                                  // the graph and the lookup must agree on one spelling
        if ($frec['inc'] || $frec['tail'] || $frec['unresolved'] || $frec['unk'] || $frec['grd'] || $frec['set'] || $frec['entry_blocked'])
            $sum['files'][$fkey] = $frec;

        foreach ($defs as [$kind, $name, $def, $cls]) {
            if ($def->stmts === null) continue;                       // abstract / interface
            $params = [];
            foreach ($def->params as $p) { $n = ($p->var instanceof Expr\Variable && is_string($p->var->name)) ? $p->var->name : null; $params[] = $n; }
            $np = count($params);
            $rec = ['file' => $f, 'line' => $def->getStartLine(), 'params' => $np,
                    'passes' => [], 'opaque' => [], 'substitutes' => [], 'sinks' => [], 'guard' => [], 'cut' => false,
                    'ends' => bodyEnds($def->stmts)];
            $probes = array_merge([-2], ($np === 0) ? [] : (($np <= 4) ? range(0, $np - 1) : [-1]));   // -2: none tainted; -1: all at once
            foreach ($probes as $ix) {
                $an = new Analyzer($CAT);
                foreach ($litWrites as $vn => $rhs)
                    if (count($rhs) === 1 && $rhs[0] !== null && Analyzer::isLiteralPublic($rhs[0])) $an->lits[$vn] = $rhs[0];
                $an->currentClassPublic($cls);
                $env = [];
                foreach ($params as $j => $pn) {
                    if ($pn === null) continue;
                    $env[$pn] = ($ix === -1 || $ix === $j) ? stT('param', '$' . $pn, $def->getStartLine()) : stF();
                }
                $ret = $an->probeBody($def->stmts, $env);
                if ($an->nodeSpent > 120000 || $an->inlineSpent >= 3000) { $rec['cut'] = true; }
                // THE BODY'S OWN SOURCES (xown, 2026-09-11). With no argument tainted, what comes back is what the function
                // produces BY ITSELF: `function f($x){ return $_GET['a']; }` returns request data whatever it is given. The summary
                // described arguments only, so `echo f('c')` — and dolibarr's `print GETPOST('x', 'none')` — read EARNED,
                // "constants only", and every sink the body reached on its own was charged to whichever argument was probed.
                // A walk cut short does not vouch for a clean result: Z.
                if ($ix === -2) {
                    $cutNow = $an->nodeSpent > 120000 || $an->inlineSpent >= 3000;
                    $rec['own'] = $ret['t'] === 'T' ? 'T' : (($ret['t'] === 'Z' || $cutNow) ? 'Z' : 'F');
                    if ($rec['own'] === 'T' && $ret['san']) $rec['own_san'] = array_keys($ret['san']);
                    continue;
                }
                $probeSrc = [];
                foreach ($params as $j => $pn) if ($pn !== null && ($ix === -1 || $ix === $j)) $probeSrc[] = ['param', '$' . $pn, $def->getStartLine()];
                $key = $ix === -1 ? 'any' : (string)$ix;
                // THREE OUTCOMES, kept apart because they mean different things to the caller:
                //   passes  — the result carries this argument's taint, and what substitutes it is named
                //   opaque  — the result is Z: something inside was unreadable, so the caller gets Z too
                //   clean   — the result does not carry it at all (a real sanitizer, or an unrelated return)
                if ($ret['t'] === 'T' && srcMeets($ret['src'] ?? [], $probeSrc)) {
                    $rec['passes'][] = $key;
                    $ctxs = array_keys($ret['san']);
                    if ($ctxs) $rec['substitutes'][$key] = $ctxs;
                } elseif ($ret['t'] === 'Z') {
                    $rec['opaque'][] = $key;
                }
                // ONLY A SINK THAT WOULD BE REFUTED INSIDE. A callee that binds or escapes the value
                // before its query is not a hole the caller inherits: WordPress's
                // wpmu_validate_user_signup() reaches $wpdb->get_row, but through $wpdb->prepare with
                // %s. Recording that as "argument 0 reaches an sql sink" produced 73 accusations
                // against WordPress in one run, every one wrong. Measured 2026-09-09.
                foreach ($an->facts as $fact) {
                    // ONLY WHAT THE ARGUMENT ITSELF REACHES. A `Z` at the sink means the trail was lost
                    // inside the callee — an unknown call, another file's helper — not that this
                    // parameter arrived there. Recording Z as "reaches a sink" made the caller answer
                    // for a path we had already admitted we could not follow: 10 of WordPress's 52 were
                    // wp_dropdown_languages, whose echo receives a string built through selected() and
                    // wp_parse_args, both opaque to a single-file walk. Measured 2026-09-09.
                    if (($fact['t'] ?? 'F') !== 'T') continue;
                    if (!srcMeets($fact['src'] ?? [], $probeSrc)) continue;          // the body's own source reached it, not this argument
                    $fs = is_array($fact['san'] ?? null) ? $fact['san'] : [];
                    $ctx = $fact['ctx'];
                    if (isset($fs['*'])) continue;                                  // substituted for every context
                    if (isset($fs[$ctx])) continue;                                 // substituted for this one
                    if ($ctx === 'sql' && isset($fs['sql-quoted']) && ($fact['q'] ?? null) === true) continue;
                    $rec['sinks'][] = [$key, $ctx];
                }
                if ($ret['t'] === 'F' && $an->returnedBool) $rec['guard'][] = $key;
            }
            $rec['sinks'] = uniq($rec['sinks']);
            // TWO DEFINITIONS UNDER ONE NAME (the blog engine defines __() three times, safe() twice): a summary that
            // silently kept the last one would credit a call with what a DIFFERENT function does. If they disagree on
            // anything but file/line, the name is a CONFLICT and reads as unknown in pass 2.
            $slot = $kind === 'fn' ? 'functions' : 'methods';
            $k = $kind === 'fn' ? $name : strtolower($cls) . '::' . $name;
            $sum[$slot][$k] = summaryMerge($sum[$slot][$k] ?? null, $rec);
            // ALSO by bare name, under the same merge rule: if every definition of `trans` in the tree does
            // the same thing to a tainted argument, WHICH one runs does not matter. Read only when
            // --assume-tree-methods says the callee is in the tree; the default does not assume it.
            if ($kind === 'm') $sum['byname'][$name] = summaryMerge($sum['byname'][$name] ?? null, $rec);
        }
    }
    emit($sum, 0);
    exit(0);
}

emit($out, JSON_PRETTY_PRINT);
