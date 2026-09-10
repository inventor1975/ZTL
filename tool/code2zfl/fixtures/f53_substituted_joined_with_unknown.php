<?php
// a substituted attacker value joined with a value of unknown origin (a directory listing, a call past the depth cap):
// the substitution stands and the unknown part is the weak link — OPEN, never "read in full" REFUTED after array_merge.
// EXPECT: EARNED, OPEN, EARNED — the FIRST is `scandir`, a sink since 2026-09-10 (f89): the directory it
// lists is chosen by the request, and here that choice went through preg_replace-strip, so it earns.
$t = preg_replace('/[^A-Za-z0-9_\-]/', '', $_GET['tpl']);
$paths = array();
foreach (scandir("/srv/templates/" . $t) as $entry) {
    $paths[] = "/srv/templates/" . $t . "/" . $entry;
}
$all = array_merge($paths, array());
foreach ($all as $p) {
    file_get_contents($p);
}
file_get_contents("/srv/templates/" . $t . "/index.php");
