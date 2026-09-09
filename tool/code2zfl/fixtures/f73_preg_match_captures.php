<?php
// `preg_match($pat, $subject, $matches)` WRITES THE SUBJECT'S OWN SUBSTRINGS into $matches. Reading
// $matches as `unassigned` was a MISS: a pattern that confines nothing puts the request straight into
// $m[1]. A capture is a narrowing of the subject — only `*` survives it — and a pattern we read AND
// find CONFINING is itself the substitution. Anchors are a GUARD's question, not a capture's: what a
// capture holds is drawn from the pattern's own language whether or not the subject was anchored, so
// `~([A-Za-z0-9_-]+)~` confines it. A group without alternation adds nothing to the language. A
// pattern we cannot read leaves the subject exactly as it was.
// EXPECT: REFUTED, EARNED, REFUTED, EARNED
preg_match('/x(.*)/', $_SERVER['REQUEST_URI'], $m);
unlink('/srv/' . $m[1]);
preg_match('/^([a-z]+)$/', $_GET['q'], $g);
unlink('/srv/' . $g[1]);
preg_match($somePattern, $_GET['r'], $h);
unlink('/srv/' . $h[1]);
preg_match('~([A-Za-z0-9_-]+)~', $_GET['s'], $u);
unlink('/srv/' . $u[1]);
