<?php
// WRITING ONE KEY OF AN ARRAY DOES NOT TAINT THE OTHERS — the rule properties got the same day.
// `$GLOBALS['a'] = $_GET['x']` used to be joined into the whole array, so `$GLOBALS['b']`, written
// nowhere near it, read as attacker-controlled. Reading the array AS A WHOLE still sees every slot,
// and a COMPUTED key taints it entirely, because which element it was is exactly what we do not know.
// EXPECT: REFUTED, EARNED, REFUTED, REFUTED
$a = [];
$a['t'] = $_GET['x'];
unlink('/srv/' . $a['t']);
unlink('/srv/' . $a['other']);
unlink('/srv/' . implode('', $a));
$b = [];
$b[$_GET['k']] = $_GET['v'];
unlink('/srv/' . $b['anything']);
