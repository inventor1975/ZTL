<?php
// A singleton reached THROUGH A PROPERTY — `Db::$db->query()`, `$app->db->escape()` — is its own act, and an
// overlay must be able to name it. Until 2026-09-09 the receiver key was built only for `$var->m`, `fn()->m`
// and `Class::m`, so such a call fell back to the bare method name and an overlay written for the singleton
// matched nothing at all (measured: the whole SMF overlay was inert).   EXPECT: EARNED, EARNED, REFUTED
class Reg { public static $db; }
$x = $_GET['x'];
Reg::$db->query("SELECT * FROM t WHERE a = '" . Reg::$db->escape($x) . "'");
Reg::$db->query("SELECT * FROM t WHERE b = '" . $app->db->escape($x) . "'");
Reg::$db->query("SELECT * FROM t WHERE c = '" . $x . "'");
