<?php
// WHAT IS LEFT, NOT WHAT MATCHED. `preg_replace('/\W/si', '', $x)` deletes every character outside
// [A-Za-z0-9_], so what remains provably carries no quote, slash or angle bracket: the element is
// replaced by one drawn from an alphabet we read. A NON-negated class does the opposite — it removes
// the safe characters and keeps the rest. A replacement that is itself dangerous settles nothing, and
// a pattern we cannot read is a transformation, not a substitution.
// EXPECT: EARNED, EARNED, REFUTED, REFUTED, REFUTED
$a = preg_replace('/\W/si', '', $_GET['a']);
unlink('/srv/' . $a);
$b = preg_replace('/[^a-z0-9]/', '', $_GET['b']);
unlink('/srv/' . $b);
$c = preg_replace('/[a-z]/', '', $_GET['c']);
unlink('/srv/' . $c);
$d = preg_replace('/\W/', '/', $_GET['d']);
unlink('/srv/' . $d);
$e = preg_replace($somePattern, '', $_GET['e']);
unlink('/srv/' . $e);
