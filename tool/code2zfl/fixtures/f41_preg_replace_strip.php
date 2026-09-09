<?php
// preg_replace('/[^a-z0-9]/', '', $x) confines the value to that class — a substitution by construction;
// removing only the quote is not (a backslash still passes).  EXPECT: EARNED, REFUTED
$a = preg_replace('/[^a-zA-Z0-9_]/', '', $_GET['a']);
$db->query("SELECT * FROM posts WHERE alias = '" . $a . "'");
$b = preg_replace("/'/", '', $_GET['b']);
$db->query("SELECT * FROM posts WHERE alias = '" . $b . "'");
