<?php
// a substituted attacker value joined with a value of unknown origin (a directory listing, a call past the depth cap):
// the substitution stands and the unknown part is the weak link — OPEN, never "read in full" REFUTED after array_merge.
// EXPECT: OPEN, EARNED
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
