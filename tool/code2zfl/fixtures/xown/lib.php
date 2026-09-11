<?php
// xown (2026-09-11): what a function produces BY ITSELF comes back whatever it is given; a sink its own source reaches is not
// its arguments' sink. The summary used to describe arguments only.
function f($x) { return $_GET['a']; }
function g() { return $_GET['b']; }
function h($x) { include $_GET['c']; return 1; }
function k($x) { return htmlspecialchars($_GET['q'], ENT_QUOTES); }
function m($x) { return $x; }
