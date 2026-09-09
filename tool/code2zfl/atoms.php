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
$files = [];
$phpVersion = null;                       // e.g. 7.4 — legacy syntax the newest grammar refuses
for ($i = 1; $i < $argc; $i++) {
    $a = $argv[$i];
    if ($a === '--autoload') { $autoload = $argv[++$i]; continue; }
    if ($a === '--catalog')  { $catalogPath = $argv[++$i]; continue; }
    if ($a === '--overlay')  { $overlays[] = $argv[++$i]; continue; }
    if ($a === '--php')      { $phpVersion = $argv[++$i]; continue; }
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
$CAT = loadJson($catalogPath);
foreach ($overlays as $o) $CAT = mergeCatalog($CAT, loadJson($o));

$lowerKey = fn(string $k) => (str_contains($k, '->') || str_contains($k, '::')) ? preg_replace_callback('/(->|::)([^>:]+)$/', fn($m) => $m[1] . strtolower($m[2]), $k) : strtolower($k);
$SUPER = array_flip($CAT['sources']['superglobals'] ?? []);
$SERVER_KEYS = $CAT['sources']['server_keys'] ?? [];   // which $_SERVER entries an attacker can write
$SERVER_PREFIXES = $CAT['sources']['server_prefixes'] ?? [];
$SRCFN = array_flip(array_map('strtolower', $CAT['sources']['functions'] ?? []));
$SRCMETH = array_flip(array_map($lowerKey, $CAT['sources']['methods'] ?? []));   // "$obj->name", "Class::name", "fn()->name" keys allowed
$SANFN = array_change_key_case($CAT['sanitizers']['functions'] ?? [], CASE_LOWER);
$SANMETH = []; foreach ($CAT['sanitizers']['methods'] ?? [] as $k => $v) $SANMETH[$lowerKey($k)] = $v;
$SANCAST = $CAT['sanitizers']['casts'] ?? [];
$TRANSP = array_flip(array_map('strtolower', $CAT['transparent'] ?? []));
$GUARDS = array_change_key_case($CAT['guards'] ?? [], CASE_LOWER);   // a condition that VERIFIES a value
$PRESERV = array_flip(array_map('strtolower', $CAT['preserving'] ?? []));
$NARROW = array_flip(array_map('strtolower', $CAT['narrowing'] ?? []));
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
function stF(): array { return ['t' => 'F', 'src' => [], 'san' => [], 'z' => [], 'q' => null, 'zu' => [], 'nu' => false, 'dv' => []]; }
function stZ(string $why, int $line): array { return ['t' => 'Z', 'src' => [], 'san' => [], 'z' => [[$why, $line]], 'q' => null, 'zu' => [], 'nu' => false, 'dv' => []]; }
function stT(string $kind, string $name, int $line): array { return ['t' => 'T', 'src' => [[$kind, $name, $line]], 'san' => [], 'z' => [], 'q' => null, 'zu' => [], 'nu' => true, 'dv' => ['#src']]; }
function dvUnion(array $a, array $b): array { return array_values(array_unique(array_merge($a['dv'] ?? [], $b['dv'] ?? []))); }

function uniq(array $rows): array {
    $seen = []; $out = [];
    foreach ($rows as $r) { $k = json_encode($r); if (!isset($seen[$k])) { $seen[$k] = 1; $out[] = $r; } }
    return $out;
}
/** JOIN of two paths: may-taint, must-sanitize. */
function join2(array $a, array $b): array {
    $t = RANK[$a['t']] >= RANK[$b['t']] ? $a['t'] : $b['t'];
    if ($a['t'] === 'F') $san = $b['san'];
    elseif ($b['t'] === 'F') $san = $a['san'];
    else $san = sanMeet($a['san'], $b['san']);
    $qa = $a['t'] === 'F' ? null : $a['q']; $qb = $b['t'] === 'F' ? null : $b['q'];   // constants have no quoting question
    if ($qa === false || $qb === false) $q = false;
    elseif ($qa === null) $q = $qb; elseif ($qb === null) $q = $qa; else $q = true;
    return ['t' => $t, 'src' => uniq(array_merge($a['src'], $b['src'])), 'san' => $san,
            'z' => uniq(array_merge($a['z'], $b['z'])), 'q' => $q,
            'zu' => uniq(array_merge($a['zu'] ?? [], $b['zu'] ?? [])), 'nu' => ($a['nu'] ?? false) || ($b['nu'] ?? false), 'dv' => dvUnion($a, $b)];
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
            'nu' => ($s['nu'] ?? false) || ($keep !== 'all' && $s['t'] === 'T' && !$san), 'dv' => $s['dv'] ?? []];
    // an UNKNOWN call's result is not visible here even when every argument is a constant: `$obj->get()` reads
    // the object's state, `time()` reads the clock — before 2026-09-09 such a call over constants stayed F and
    // four in-file getter shapes of the SARD suite came back EARNED ("nothing arrives") instead of OPEN
    if ($unknown) { $out['t'] = 'Z'; $out['z'][] = [$why, $line]; $out['nu'] = false; }
    return $out;
}
function sanitize(array $s, array $ctxs, string $fn, int $line): array {
    // a NUMERIC substitution of the whole value settles every part inside it; a context escape of a
    // built string does not settle a part of unknown origin that may sit outside the quotes
    $zu = in_array('*', $ctxs, true) ? [] : ($s['zu'] ?? []);
    $out = ['t' => $s['t'], 'src' => $s['src'], 'san' => $s['san'], 'z' => $s['z'], 'q' => null, 'zu' => $zu, 'nu' => false, 'dv' => $s['dv'] ?? []];
    foreach ($ctxs as $c) $out['san'][$c] = [$fn, $line];
    return $out;
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
    public array $callers = [];                       // 'fn:name' | 'm:Class::name' -> in-file call sites
    public array $props = [];                         // class -> prop -> state
    public int $pass = 1;
    private array $callStack = [];
    private array $returns = [];
    private ?string $currentClass = null;
    private int $callDepth = 3;

    /** filter flags whose PASS leaves a value in a fixed alphabet: int, float, bool, IP (digits, dots, colons, a-f). EMAIL and URL let a quote through. */
    private const VALIDATE_FIXED = ['FILTER_VALIDATE_INT', 'FILTER_VALIDATE_FLOAT', 'FILTER_VALIDATE_BOOL', 'FILTER_VALIDATE_BOOLEAN', 'FILTER_VALIDATE_IP'];
    /** name -> literal node, for variables assigned EXACTLY ONCE in the file from a literal (`$re = "/^[0-9]+$/"`,
     *  `$allowed = array(...)`): a guard may read them as the fixed set/pattern they are. Filled before the walk. */
    public array $lits = [];

    public function __construct(private array $cat) {}

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
        if ($e instanceof Scalar\String_) return [['lit', self::quoteCounts($e->value)]];
        if ($e instanceof Scalar\InterpolatedString) {
            $out = [];
            foreach ($e->parts as $p) {
                if ($p instanceof Node\InterpolatedStringPart) $out[] = ['lit', self::quoteCounts($p->value)];
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
                    $parts[] = ['lit', self::quoteCounts(substr($val, $pos, $mm[0][1] - $pos))];
                    $pos = $mm[0][1] + strlen($mm[0][0]);
                    $conv = $mm[2][0];
                    if ($conv === '%') continue;
                    $ix = ($mm[1][0] !== '' && $mm[1][1] >= 0) ? (int)$mm[1][0] - 1 : $next++;
                    $a = $args[$ix] ?? stZ('sprintf-arg-missing', $line);
                    $parts[] = ['expr', ($conv === 's' || $conv === 'c') ? $a : sanitize($a, ['*'], 'sprintf-%' . $conv, $line)];
                }
            }
            $parts[] = ['lit', self::quoteCounts(substr($val, $pos))];
        }
        return $this->concatParts($parts);
    }

    private function concatParts(array $parts): array {
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
    private static function slot(Expr $target): ?string {
        if (!($target instanceof Expr\ArrayDimFetch) || !($target->var instanceof Expr\Variable) || !is_string($target->var->name)) return null;
        $d = $target->dim;
        if ($d instanceof Scalar\String_) return $target->var->name . '[' . $d->value . ']';
        if ($d instanceof Scalar\Int_) return $target->var->name . '[' . $d->value . ']';
        return null;
    }

    private function sinkFact(string $ctx, string $fn, int $line, array $s): void {
        $this->facts[] = ['ctx' => $ctx, 'fn' => $fn, 'line' => $line, 'scope' => $this->scope,
                          't' => $s['t'], 'src' => $s['src'], 'san' => $s['san'], 'z' => $s['z'], 'q' => $s['q'], 'zu' => $s['zu'] ?? [], 'nu' => $s['nu'] ?? false];
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
        global $SUPER, $SERVER_KEYS, $SERVER_PREFIXES, $GUARDS, $SRCFN, $SRCMETH, $SANFN, $SANMETH, $SANCAST, $TRANSP, $PRESERV, $NARROW, $SINKFN, $SINKMETH, $SINKARG, $SINKFLAGS;
        if ($e === null) return stF();
        $line = $e->getStartLine();

        if ($e instanceof Scalar\String_ || $e instanceof Scalar\Int_ || $e instanceof Scalar\Float_
            || $e instanceof Scalar\MagicConst || $e instanceof Expr\ConstFetch || $e instanceof Expr\ClassConstFetch) return stF();
        if ($e instanceof Scalar\InterpolatedString || $e instanceof Expr\BinaryOp\Concat) return $this->concat($e, $env);

        if ($e instanceof Expr\Variable) {
            if (!is_string($e->name)) { return stZ('variable-variable', $line); }
            if (isset($SUPER[$e->name])) return stT('superglobal', '$' . $e->name, $line);
            if ($e->name === 'this') return stF();
            if (!isset($env[$e->name])) return stZ('unassigned:$' . $e->name, $line);
            $st = $env[$e->name]; $st['dv'] = [$e->name]; return $st;           // the DIRECT parent of what is read is this variable
        }
        if ($e instanceof Expr\ArrayDimFetch) {
            $this->ex($e->dim, $env);
            // $_SERVER is attacker-written only in part: HTTP_* headers, the request line and path — not
            // REMOTE_ADDR or SERVER_*. A literal key is CLASSIFIED here and never emitted.
            if ($e->var instanceof Expr\Variable && $e->var->name === '_SERVER' && isset($SUPER['_SERVER'])) {
                if ($e->dim instanceof Scalar\String_) {
                    $k = $e->dim->value;
                    $hot = in_array($k, $SERVER_KEYS, true);
                    foreach ($SERVER_PREFIXES as $pfx) if (str_starts_with($k, $pfx)) $hot = true;
                    return $hot ? stT('superglobal', '$_SERVER', $line) : stF();
                }
                return stT('superglobal', '$_SERVER', $line);                       // a computed key: assume the worst
            }
            $sl = self::slot($e);
            if ($sl !== null && isset($env[$sl])) { $st = $env[$sl]; $st['dv'] = [$sl]; return $st; }   // this key was written here: read that, not the whole array
            if ($sl !== null && isset($env[$e->var->name])) { $st = $this->ex($e->var, $env); $st['dv'] = [$sl]; return $st; }   // an element never written here: the whole array's state, under the element's name
            $base = $this->ex($e->var, $env);
            return $base;
        }
        if ($e instanceof Expr\PropertyFetch || $e instanceof Expr\NullsafePropertyFetch || $e instanceof Expr\StaticPropertyFetch) {
            if ($e instanceof Expr\PropertyFetch && $e->var instanceof Expr\Variable && $e->var->name === 'this'
                && $e->name instanceof Node\Identifier && $this->currentClass !== null) {
                $pn = $e->name->toString();
                if (isset($this->props[$this->currentClass][$pn])) return $this->props[$this->currentClass][$pn];
                return stZ('property:$this->' . $pn, $line);
            }
            // another object's property: name the object, so the ledger says WHICH boundary this is
            if ($e instanceof Expr\PropertyFetch && $e->var instanceof Expr\Variable && is_string($e->var->name) && $e->name instanceof Node\Identifier)
                return stZ('property:$' . $e->var->name . '->' . $e->name->toString(), $line);
            return stZ('property', $line);
        }
        if ($e instanceof Expr\Array_) {
            $st = [];
            foreach ($e->items as $it) { if ($it === null) continue; if ($it->key) $st[] = $this->ex($it->key, $env); $st[] = $this->ex($it->value, $env); }
            return joinAll($st ?: [stF()]);
        }
        if ($e instanceof Expr\Assign || $e instanceof Expr\AssignRef) {
            $rhs = $this->ex($e->expr, $env);
            $this->assignTo($e->var, $rhs, $env, $line);
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
            $a = $e->if ? $this->ex($e->if, $env) : $c;
            $b = $this->ex($e->else, $env);
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
            if (isset($SINKFN['print'])) $this->sinkFact($SINKFN['print'], 'print', $line, $s);
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
            return joinAll($st) ['t'] === 'F' ? stF() : stZ('new', $line);
        }
        if ($e instanceof Expr\Match_) {
            $this->ex($e->cond, $env); $st = [];
            foreach ($e->arms as $arm) { foreach ($arm->conds ?? [] as $c) $this->ex($c, $env); $st[] = $this->ex($arm->body, $env); }
            return joinAll($st ?: [stF()]);
        }
        if ($e instanceof Expr\FuncCall || $e instanceof Expr\StaticCall || $e instanceof Expr\MethodCall || $e instanceof Expr\NullsafeMethodCall) {
            $isMethod = $e instanceof Expr\MethodCall || $e instanceof Expr\NullsafeMethodCall;
            if ($isMethod) $this->ex($e->var, $env);
            $name = $this->callName($e);
            $args = $this->args($e, $env);
            $recv = null;
            if ($isMethod && $e->var instanceof Expr\Variable && is_string($e->var->name)) $recv = '$' . $e->var->name . '->' . $name;
            elseif ($isMethod && $e->var instanceof Expr\FuncCall && $e->var->name instanceof Node\Name) $recv = strtolower($e->var->name->toString()) . '()->' . $name;
            elseif ($e instanceof Expr\StaticCall && $e->class instanceof Node\Name) $recv = $e->class->getLast() . '::' . $name;
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
            if ($sinkCtx !== null) {
                $ix = $SINKARG[$name] ?? 0;
                if ($fmt !== null && $name === 'printf') $this->sinkFact($sinkCtx, 'printf', $line, $fmt);   // what is printed is the FORMATTED string
                elseif (isset($args[$ix])) $this->sinkFact($sinkCtx, ($isMethod ? '->' : '') . $name, $line, $args[$ix]);
            }
            // sources
            if ($isMethod ? ($qual($SRCMETH) !== null) : ($e instanceof Expr\StaticCall ? ($qual($SRCMETH) !== null || isset($SRCFN[$name])) : isset($SRCFN[$name]))) {
                $src = stT('fn', $recv ?? (($isMethod ? '->' : '') . $name), $line);
                $flt = (!$isMethod && $name === 'filter_input') ? ($e->args[2]->value ?? null) : null;   // filter_input(INPUT_GET, 'id', FILTER_VALIDATE_INT)
                $fname = $flt instanceof Expr\ConstFetch ? strtoupper($flt->name->toString()) : '';
                return in_array($fname, self::VALIDATE_FIXED, true) ? sanitize($src, ['*'], 'filter_input:' . $fname, $line) : $src;
            }
            // sanitizers: substitution of the value for the listed contexts
            $san = $isMethod ? $qual($SANMETH) : ($e instanceof Expr\StaticCall ? ($qual($SANMETH) ?? ($SANFN[$name] ?? null)) : ($SANFN[$name] ?? null));
            if ($san !== null) {
                $ix = $san['arg'] ?? 0; if ($ix < 0) $ix = count($args) - 1;
                $s = $args[$ix] ?? stF();
                return sanitize($s, $san['contexts'], ($isMethod ? ($recv ?? '->' . $name) : $name), $line);
            }
            // defined in THIS file: inline with the caller's argument states
            if (!$isMethod && $e instanceof Expr\FuncCall && isset($this->defs['fn'][$name]))
                return $this->inline($this->defs['fn'][$name], $args, $line, 'fn:' . $name);
            if ($isMethod && $e->var instanceof Expr\Variable && $e->var->name === 'this' && $this->currentClass !== null
                && isset($this->defs['m'][$this->currentClass][$name]))
                return $this->inline($this->defs['m'][$this->currentClass][$name], $args, $line, 'm:' . $this->currentClass . '::' . $name);
            if ($e instanceof Expr\StaticCall && $e->class instanceof Node\Name && $this->currentClass !== null
                && in_array(strtolower($e->class->toString()), ['self', 'static', strtolower($this->currentClass)], true)
                && isset($this->defs['m'][$this->currentClass][$name]))
                return $this->inline($this->defs['m'][$this->currentClass][$name], $args, $line, 'm:' . $this->currentClass . '::' . $name);
            if ($fmt !== null) return $name === 'printf' ? stF() : $fmt;
            if (!$isMethod && $name === 'filter_var') {
                $flt = $e->args[1]->value ?? null;
                $fname = $flt instanceof Expr\ConstFetch ? strtoupper($flt->name->toString()) : '';
                if (in_array($fname, self::VALIDATE_FIXED, true))
                    return sanitize($args[0] ?? stF(), ['*'], 'filter_var:' . $fname, $line);
                if ($fname === 'FILTER_SANITIZE_SPECIAL_CHARS' || $fname === 'FILTER_SANITIZE_FULL_SPECIAL_CHARS')   // = htmlspecialchars
                    return sanitize($args[0] ?? stF(), ['html'], 'filter_var:' . $fname, $line);
                return through(joinAll($args ?: [stF()]), null, $line, false, 'none');
            }
            // preg_replace('/[^a-z0-9]/', '', $x): everything outside a plain class is REMOVED, so the result lives in
            // that class — a substitution by construction, the same credit as an anchored preg_match guard
            if (!$isMethod && $name === 'preg_replace' && ($e->args[0]->value ?? null) instanceof Scalar\String_
                && ($e->args[1]->value ?? null) instanceof Scalar\String_ && $e->args[1]->value->value === ''
                && self::patternStripsToClass($e->args[0]->value->value))
                return sanitize($args[2] ?? stF(), ['*'], 'preg_replace-strip', $line);
            if (!$isMethod && ($name === 'explode' || $name === 'implode' || $name === 'join')) {
                // splitting/joining on a literal delimiter that carries no quote, backslash or NUL cannot
                // strand an escape: preserving. Any other delimiter: numeric substitutions only.
                $delim = $e->args[0]->value ?? null;
                $safe = $delim instanceof Scalar\String_ && !preg_match('/[\\\\\'"\x00]/', $delim->value);
                $data = $args[1] ?? $args[0] ?? stF();
                return through($data, null, $line, false, $safe ? 'all' : 'numeric');
            }
            if (!$isMethod && isset($PRESERV[$name])) return through(joinAll($args ?: [stF()]), null, $line, false, 'all');
            if (!$isMethod && isset($NARROW[$name]))  return through(joinAll($args ?: [stF()]), null, $line, false, 'numeric');
            if (!$isMethod && isset($TRANSP[$name]))  return through(joinAll($args ?: [stF()]), null, $line, false, 'none');
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
            return stZ('shell-result', $line);
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
        if (!($n instanceof Scalar\String_)) return false;
        $p = $n->value;
        if (strlen($p) < 3) return false;
        $d = $p[0]; $end = strrpos($p, $d);
        if ($end === false || $end === 0) return false;
        $flags = substr($p, $end + 1); $body = substr($p, 1, $end - 1);
        if (str_contains($flags, 'm')) return false;
        $atom = '(?:\[[A-Za-z0-9_\\\\\-]+\]|\\\\[dw]|[A-Za-z0-9_\-])(?:[+*?]|\{\d+(?:,\d*)?\})?';
        $re = '/^(?:\^|\\\\A)(?:' . $atom . ')+(?:\$|\\\\[zZ])$/';
        return (bool)preg_match($re, $body);
    }

    /** What a condition VERIFIES: ['true' => [[var, contexts, fn, line]...], 'false' => [...]].
     *  A guard is an act of checking, and inside the branch it protects the value is substituted (E40:
     *  the sanitizer is a substitution, and a verified membership in a fixed set is one). */
    private function guards(Expr $c): array {
        global $GUARDS;
        $line = $c->getStartLine();
        $none = ['true' => [], 'false' => []];
        if ($c instanceof Expr\BooleanNot) { $g = $this->guards($c->expr); return ['true' => $g['false'], 'false' => $g['true']]; }
        if ($c instanceof Expr\BinaryOp\BooleanAnd || $c instanceof Expr\BinaryOp\LogicalAnd) {
            $l = $this->guards($c->left); $r = $this->guards($c->right);
            return ['true' => array_merge($l['true'], $r['true']), 'false' => []];
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
            $v = $this->varName($adf->dim ?? null);
            if ($v !== null && ($adf->var instanceof Expr\ConstFetch || $adf->var instanceof Expr\ClassConstFetch)) return ['true' => [[$v, ['*'], 'isset-fixed-map', $line]], 'false' => []];
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
            if ($g === null) return $none;
            $vix = $g['value'] ?? 0;
            $v = isset($args[$vix]) ? $this->guardName($args[$vix]->value) : null;
            if ($v === null) return $none;
            if (isset($g['haystack']) && $this->litOf($args[$g['haystack']]->value ?? null) === null) return $none;   // in_array($x, $unknown): no
            if (!empty($g['pattern_tight']) && !self::patternIsTight($this->litOf($args[$g['pattern']]->value ?? null))) return $none;
            return ['true' => [[$v, $g['contexts'], 'guard:' . $fn, $line]], 'false' => []];
        }
        if ($c instanceof Expr\Assign) return $this->guards($c->expr);   // if ($m = preg_match(...)) — rare; keep simple
        return $none;
    }

    private function applyGuards(array $gs, array &$env): void {
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

    private function assignTo(Expr $target, array $rhs, array &$env, int $line): void {
        if ($target instanceof Expr\Variable) {
            $n = $this->varName($target);
            if ($n !== null) { $env[$n] = $rhs; foreach (array_keys($env) as $k) if (str_starts_with($k, $n . '[')) unset($env[$k]); }   // a fresh array: its old slots are gone
            else $this->ex($target, $env);
            return;
        }
        if ($target instanceof Expr\ArrayDimFetch) {
            $this->ex($target->dim, $env);
            $root = $target; while ($root instanceof Expr\ArrayDimFetch) $root = $root->var;
            $n = $this->varName($root);
            if ($n !== null) {
                $cur = $env[$n] ?? stF(); $j = join2($cur, $rhs);
                $sl = self::slot($target);
                if ($sl !== null) { $env[$sl] = $rhs; if ($cur['t'] !== 'F') $j['nu'] = false; }   // the element is read from its slot; the whole array is a may-join, not "read in full"
                $env[$n] = $j;
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
            $cur = $this->props[$this->currentClass][$pn] ?? null;
            $this->props[$this->currentClass][$pn] = $cur === null ? $rhs : join2($cur, $rhs);
            return;
        }
        // other objects' properties, static properties: not tracked
    }

    /** Analyse a callee body with the caller's argument states; sinks inside are emitted in the caller's
     *  context, the joined `return` state comes back. Depth-capped and recursion-cut: past the cap the call
     *  is what it was before — unknown. */
    private function inline(Node $def, array $args, int $line, string $key): array {
        if (count($this->callStack) >= $this->callDepth || in_array($key, $this->callStack, true))
            return through(joinAll($args ?: [stF()]), 'call-depth:' . $key, $line, true);
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

    private static function joinEnv(array $envs, array $pre): array {
        $names = [];
        foreach ($envs as $e) foreach ($e as $k => $_) $names[$k] = 1;
        $out = [];
        foreach (array_keys($names) as $k) {
            $st = []; $arr = ($p = strpos($k, '[')) !== false ? substr($k, 0, $p) : null;
            foreach ($envs as $e) $st[] = $e[$k] ?? ($pre[$k] ?? ($arr !== null ? ($e[$arr] ?? $pre[$arr] ?? stZ('maybe-unassigned:$' . $arr . '[…]', 0)) : stZ('maybe-unassigned:$' . $k, 0)));
            $out[$k] = joinAll($st);
        }
        return $out;
    }
    private static function envEq(array $a, array $b): bool { return json_encode($a) === json_encode($b); }

    public function walk(array $stmts, array &$env): void {
        foreach ($stmts as $s) $this->stmt($s, $env);
    }

    private function stmt(Node $s, array &$env): void {
        global $SINKFLAGS;
        $line = $s->getStartLine();
        if ($s instanceof Stmt\Expression) { $this->ex($s->expr, $env); return; }
        if ($s instanceof Stmt\Echo_) {
            foreach ($s->exprs as $x) { $st = $this->ex($x, $env); if (isset($SINKFLAGS['echo'])) $this->sinkFact($SINKFLAGS['echo'], 'echo', $line, $st); }
            return;
        }
        if ($s instanceof Stmt\Return_) { $st = $s->expr ? $this->ex($s->expr, $env) : stF(); if ($this->returns) $this->returns[count($this->returns) - 1][] = $st; return; }
        if ($s instanceof Stmt\If_) {
            $this->ex($s->cond, $env);
            $g = $this->guards($s->cond);
            $paths = [];
            $e1 = $env; $this->applyGuards($g['true'], $e1); $this->walk($s->stmts, $e1);
            $leaves = self::terminates($s->stmts);
            if (!$leaves) $paths[] = $e1;
            foreach ($s->elseifs as $ei) { $e2 = $env; $this->applyGuards($g['false'], $e2); $this->ex($ei->cond, $e2); $this->applyGuards($this->guards($ei->cond)['true'], $e2); $this->walk($ei->stmts, $e2); if (!self::terminates($ei->stmts)) $paths[] = $e2; }
            if ($s->else) { $e3 = $env; $this->applyGuards($g['false'], $e3); $this->walk($s->else->stmts, $e3); if (!self::terminates($s->else->stmts)) $paths[] = $e3; }
            else { $e0 = $env; $this->applyGuards($g['false'], $e0); $paths[] = $e0; }   // the fall-through path: the condition failed
            $env = $paths ? self::joinEnv($paths, $env) : $env;
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
            foreach ($s->cases as $c) {
                if ($c->cond === null) $hasDefault = true; else $this->ex($c->cond, $env);
                $e1 = $prev === null ? $env : self::joinEnv([$env, $prev], $env);
                if ($subj !== null && $c->cond !== null && self::isLiteral($c->cond) && isset($e1[$subj])) $e1[$subj] = sanitize($e1[$subj], ['*'], 'case-literal', $c->getStartLine());
                $this->walk($c->stmts, $e1);
                $paths[] = $e1; $prev = $e1;
            }
            if (!$hasDefault) $paths[] = $env;
            $env = self::joinEnv($paths ?: [$env], $env);
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
            $inner = [];
            foreach ($s->params as $p) { $n = $this->varName($p->var); if ($n !== null) $inner[$n] = stZ('param:$' . $n, $line); }
            $save = $this->scope; $this->scope = ($s instanceof Stmt\ClassMethod ? $save . '::' : '') . $s->name->toString() . '()';
            $key = $s instanceof Stmt\ClassMethod ? 'm:' . ($this->currentClass ?? '?') . '::' . strtolower($s->name->toString()) : 'fn:' . strtolower($s->name->toString());
            $this->functions[] = ['scope' => $this->scope, 'callers' => $this->callers[$key] ?? 0];
            $this->returns[] = [];
            if ($s->stmts !== null) $this->walk($s->stmts, $inner);
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
        if ($s instanceof Stmt\InlineHTML || $s instanceof Stmt\Nop || $s instanceof Stmt\Use_ || $s instanceof Stmt\Const_
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
    $env = [];
    $an->pass = 1; $an->walk($ast ?? [], $env);
    $an->facts = []; $an->includes = []; $an->functions = [];
    $env = [];
    $an->pass = 2; $an->walk($ast ?? [], $env);
    // a loop body is walked more than once (fixed point): one sink call site, one fact — states JOINED
    $byKey = [];
    foreach ($an->facts as $f) {
        $k = $f['ctx'] . '|' . $f['fn'] . '|' . $f['line'] . '|' . $f['scope'];
        if (!isset($byKey[$k])) { $byKey[$k] = $f; continue; }
        $j = join2($byKey[$k], $f);
        foreach (['t', 'src', 'san', 'z', 'q', 'zu', 'nu'] as $c) $byKey[$k][$c] = $j[$c];
    }
    $rec['sinks'] = array_values($byKey); $rec['includes'] = array_values(array_unique($an->includes)); $rec['functions'] = $an->functions;
    $out['files'][] = $rec;
}
echo json_encode($out, JSON_UNESCAPED_UNICODE | JSON_UNESCAPED_SLASHES | JSON_PRETTY_PRINT), "\n";
