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

$SUPER = array_flip($CAT['sources']['superglobals'] ?? []);
$SERVER_KEYS = $CAT['sources']['server_keys'] ?? [];   // which $_SERVER entries an attacker can write
$SERVER_PREFIXES = $CAT['sources']['server_prefixes'] ?? [];
$SRCFN = array_flip(array_map('strtolower', $CAT['sources']['functions'] ?? []));
$SRCMETH = array_flip(array_map('strtolower', $CAT['sources']['methods'] ?? []));
$SANFN = array_change_key_case($CAT['sanitizers']['functions'] ?? [], CASE_LOWER);
$SANMETH = array_change_key_case($CAT['sanitizers']['methods'] ?? [], CASE_LOWER);
$SANCAST = $CAT['sanitizers']['casts'] ?? [];
$TRANSP = array_flip(array_map('strtolower', $CAT['transparent'] ?? []));
$PRESERV = array_flip(array_map('strtolower', $CAT['preserving'] ?? []));
$NARROW = array_flip(array_map('strtolower', $CAT['narrowing'] ?? []));
$SINKFN = []; $SINKMETH = []; $SINKARG = []; $SINKFLAGS = [];
foreach ($CAT['sinks'] as $ctx => $spec) {
    foreach ($spec['functions'] ?? [] as $f) $SINKFN[strtolower($f)] = $ctx;
    foreach ($spec['methods'] ?? [] as $m) $SINKMETH[strtolower($m)] = $ctx;
    foreach ($spec['arg'] ?? [] as $f => $ix) $SINKARG[strtolower($f)] = $ix;
    foreach (['echo', 'include', 'eval'] as $fl) if (!empty($spec[$fl])) $SINKFLAGS[$fl] = $ctx;
}

// ------------------------------------------------------------------- state
// t: 'T' attacker-controlled on some path (verified) | 'Z' origin not visible here | 'F' constant
// src: [[kind, name, line]]     san: ctx => [fn, line] (held on EVERY path)
// z:   [[why, line]] opaque passes      q: true|false|null  (inside SQL quotes?)
const RANK = ['F' => 0, 'Z' => 1, 'T' => 2];
function stF(): array { return ['t' => 'F', 'src' => [], 'san' => [], 'z' => [], 'q' => null, 'zu' => []]; }
function stZ(string $why, int $line): array { return ['t' => 'Z', 'src' => [], 'san' => [], 'z' => [[$why, $line]], 'q' => null, 'zu' => []]; }
function stT(string $kind, string $name, int $line): array { return ['t' => 'T', 'src' => [[$kind, $name, $line]], 'san' => [], 'z' => [], 'q' => null, 'zu' => []]; }

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
    $q = ($a['q'] === $b['q']) ? $a['q'] : (($a['q'] === false || $b['q'] === false) ? false : null);
    return ['t' => $t, 'src' => uniq(array_merge($a['src'], $b['src'])), 'san' => $san,
            'z' => uniq(array_merge($a['z'], $b['z'])), 'q' => $q,
            'zu' => uniq(array_merge($a['zu'] ?? [], $b['zu'] ?? []))];
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
    $out = ['t' => $s['t'], 'src' => $s['src'], 'san' => $san, 'z' => $s['z'], 'q' => null, 'zu' => $s['zu'] ?? []];
    if ($unknown && $s['t'] !== 'F') { $out['t'] = 'Z'; $out['z'][] = [$why, $line]; }
    return $out;
}
function sanitize(array $s, array $ctxs, string $fn, int $line): array {
    // a NUMERIC substitution of the whole value settles every part inside it; a context escape of a
    // built string does not settle a part of unknown origin that may sit outside the quotes
    $zu = in_array('*', $ctxs, true) ? [] : ($s['zu'] ?? []);
    $out = ['t' => $s['t'], 'src' => $s['src'], 'san' => $s['san'], 'z' => $s['z'], 'q' => null, 'zu' => $zu];
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

    public function __construct(private array $cat) {}

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

    private function concat(Node $e, array &$env): array {
        $parts = $this->parts($e, $env);
        $states = []; $qs = []; $sq = 0; $dq = 0; $opaque = false; $zu = []; $sanT = null;
        foreach ($parts as $p) {
            if ($p[0] === 'lit') { $sq += $p[1][0]; $dq += $p[1][1]; continue; }
            $s = $p[1]; $states[] = $s;
            if ($s['t'] === 'F') continue;
            if ($s['t'] === 'Z' && !$s['san']) { $zu = array_merge($zu, $s['z']); }
            if ($s['t'] === 'T') { $sanT = $sanT === null ? $s['san'] : sanMeet($sanT, $s['san']); }
            if (isset($s['san']['*'])) { $opaque = $opaque || ($s['q'] === null && $s['t'] !== 'F' && false); continue; }   // a number needs no quotes
            // inside quotes iff an odd number of unescaped quotes precede this part in THIS string
            $qs[] = $opaque ? null : (($sq % 2 === 1) || ($dq % 2 === 1));
            if ($s['t'] !== 'F' && $s['san'] === [] && $s['t'] === 'T') { /* unsubstituted attacker part: quoting is moot */ }
        }
        $r = joinAll($states ?: [stF()]);
        if ($states) {
            if ($sanT !== null) $r['san'] = $sanT;                      // substitution is judged on the attacker-controlled parts
            $r['zu'] = uniq(array_merge($r['zu'] ?? [], $zu));           // parts of unknown origin without a substitution
            $r['q'] = !$qs ? null : (in_array(false, $qs, true) ? false : (in_array(null, $qs, true) ? null : true));
        }
        return $r;
    }

    private function varName(Expr $v): ?string {
        return ($v instanceof Expr\Variable && is_string($v->name)) ? $v->name : null;
    }

    private function sinkFact(string $ctx, string $fn, int $line, array $s): void {
        $this->facts[] = ['ctx' => $ctx, 'fn' => $fn, 'line' => $line, 'scope' => $this->scope,
                          't' => $s['t'], 'src' => $s['src'], 'san' => $s['san'], 'z' => $s['z'], 'q' => $s['q'], 'zu' => $s['zu'] ?? []];
    }

    private function callName(Node $c): ?string {
        if (($c instanceof Expr\FuncCall || $c instanceof Expr\StaticCall) && $c->name instanceof Node\Name) return strtolower($c->name->toString());
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
        global $SUPER, $SERVER_KEYS, $SERVER_PREFIXES, $SRCFN, $SRCMETH, $SANFN, $SANMETH, $SANCAST, $TRANSP, $PRESERV, $NARROW, $SINKFN, $SINKMETH, $SINKARG, $SINKFLAGS;
        if ($e === null) return stF();
        $line = $e->getStartLine();

        if ($e instanceof Scalar\String_ || $e instanceof Scalar\Int_ || $e instanceof Scalar\Float_
            || $e instanceof Scalar\MagicConst || $e instanceof Expr\ConstFetch || $e instanceof Expr\ClassConstFetch) return stF();
        if ($e instanceof Scalar\InterpolatedString || $e instanceof Expr\BinaryOp\Concat) return $this->concat($e, $env);

        if ($e instanceof Expr\Variable) {
            if (!is_string($e->name)) { return stZ('variable-variable', $line); }
            if (isset($SUPER[$e->name])) return stT('superglobal', '$' . $e->name, $line);
            if ($e->name === 'this') return stF();
            return $env[$e->name] ?? stZ('unassigned:$' . $e->name, $line);
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
            $base = $this->ex($e->var, $env);
            return $base;
        }
        if ($e instanceof Expr\PropertyFetch || $e instanceof Expr\NullsafePropertyFetch || $e instanceof Expr\StaticPropertyFetch) {
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
                $r = join2($cur, $rhs); $r['q'] = null;
            } else { $r = join2($cur, $rhs); $r['san']['*'] = ['arith', $line]; }
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
            if ($name === null) {                                             // $fn(...) / $obj->$m(...)
                if (!$isMethod && $e instanceof Expr\FuncCall) $this->ex($e->name, $env);
                return through(joinAll($args ?: [stF()]), 'dynamic-call', $line, true);
            }
            // sinks first: the argument as it ARRIVES
            $sinkCtx = $isMethod ? ($SINKMETH[$name] ?? null) : ($SINKFN[$name] ?? null);
            if ($sinkCtx !== null) {
                $ix = $SINKARG[$name] ?? 0;
                if (isset($args[$ix])) $this->sinkFact($sinkCtx, ($isMethod ? '->' : '') . $name, $line, $args[$ix]);
            }
            // sources
            if ($isMethod ? isset($SRCMETH[$name]) : isset($SRCFN[$name])) return stT('fn', ($isMethod ? '->' : '') . $name, $line);
            // sanitizers: substitution of the value for the listed contexts
            $san = $isMethod ? ($SANMETH[$name] ?? null) : ($SANFN[$name] ?? null);
            if ($san !== null) {
                $ix = $san['arg'] ?? 0; if ($ix < 0) $ix = count($args) - 1;
                $s = $args[$ix] ?? stF();
                return sanitize($s, $san['contexts'], ($isMethod ? '->' : '') . $name, $line);
            }
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

    private function assignTo(Expr $target, array $rhs, array &$env, int $line): void {
        if ($target instanceof Expr\Variable) {
            $n = $this->varName($target);
            if ($n !== null) $env[$n] = $rhs; else $this->ex($target, $env);
            return;
        }
        if ($target instanceof Expr\ArrayDimFetch) {
            $this->ex($target->dim, $env);
            $root = $target; while ($root instanceof Expr\ArrayDimFetch) $root = $root->var;
            $n = $this->varName($root);
            if ($n !== null) { $cur = $env[$n] ?? stF(); $env[$n] = join2($cur, $rhs); }
            return;
        }
        if ($target instanceof Expr\List_ || $target instanceof Expr\Array_) {
            foreach ($target->items as $it) { if ($it && $it->value instanceof Expr) $this->assignTo($it->value, through($rhs, null, $line, false, 'all'), $env, $line); }
            return;
        }
        // property / static property: not tracked
    }

    private static function joinEnv(array $envs, array $pre): array {
        $names = [];
        foreach ($envs as $e) foreach ($e as $k => $_) $names[$k] = 1;
        $out = [];
        foreach (array_keys($names) as $k) {
            $st = [];
            foreach ($envs as $e) $st[] = $e[$k] ?? ($pre[$k] ?? stZ('maybe-unassigned:$' . $k, 0));
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
        if ($s instanceof Stmt\Return_) { if ($s->expr) $this->ex($s->expr, $env); return; }
        if ($s instanceof Stmt\If_) {
            $this->ex($s->cond, $env);
            $paths = [];
            $e1 = $env; $this->walk($s->stmts, $e1); $paths[] = $e1;
            foreach ($s->elseifs as $ei) { $e2 = $env; $this->ex($ei->cond, $e2); $this->walk($ei->stmts, $e2); $paths[] = $e2; }
            if ($s->else) { $e3 = $env; $this->walk($s->else->stmts, $e3); $paths[] = $e3; } else $paths[] = $env;
            $env = self::joinEnv($paths, $env);
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
            foreach ($s->cases as $c) {
                if ($c->cond === null) $hasDefault = true; else $this->ex($c->cond, $env);
                $e1 = $prev === null ? $env : self::joinEnv([$env, $prev], $env);
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
            $this->functions[] = $this->scope;
            if ($s->stmts !== null) $this->walk($s->stmts, $inner);
            $this->scope = $save;
            return;
        }
        if ($s instanceof Stmt\Class_ || $s instanceof Stmt\Trait_ || $s instanceof Stmt\Interface_ || $s instanceof Stmt\Enum_) {
            $save = $this->scope; $this->scope = ($s->name ? $s->name->toString() : 'anon-class');
            foreach ($s->stmts as $m) { if ($m instanceof Stmt\ClassMethod) $this->stmt($m, $env); }
            $this->scope = $save;
            return;
        }
        if ($s instanceof Stmt\Global_) { foreach ($s->vars as $v) { $n = $this->varName($v); if ($n !== null) $env[$n] = stZ('global:$' . $n, $line); } return; }
        if ($s instanceof Stmt\Static_) { foreach ($s->vars as $v) { $n = $this->varName($v->var); if ($n !== null) $env[$n] = stZ('static:$' . $n, $line); } return; }
        if ($s instanceof Stmt\Unset_) { foreach ($s->vars as $v) { $n = $this->varName($v); if ($n !== null) unset($env[$n]); } return; }
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
    $env = [];
    $an->walk($ast ?? [], $env);
    // a loop body is walked more than once (fixed point): one sink call site, one fact — states JOINED
    $byKey = [];
    foreach ($an->facts as $f) {
        $k = $f['ctx'] . '|' . $f['fn'] . '|' . $f['line'] . '|' . $f['scope'];
        if (!isset($byKey[$k])) { $byKey[$k] = $f; continue; }
        $j = join2($byKey[$k], $f);
        foreach (['t', 'src', 'san', 'z', 'q', 'zu'] as $c) $byKey[$k][$c] = $j[$c];
    }
    $rec['sinks'] = array_values($byKey); $rec['includes'] = array_values(array_unique($an->includes)); $rec['functions'] = $an->functions;
    $out['files'][] = $rec;
}
echo json_encode($out, JSON_UNESCAPED_UNICODE | JSON_UNESCAPED_SLASHES | JSON_PRETTY_PRINT), "\n";
