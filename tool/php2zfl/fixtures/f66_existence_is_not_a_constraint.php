<?php
// READ AND FOUND WANTING is not an unknown check. file_exists() answers whether a path is on disk — it does
// not confine the path to one this code named, and an attacker's upload, a log and /etc/passwd are all on
// disk. is_string() fixes the type and forbids no quote; is_array()/count() say nothing about the elements.
// So these are no guard at all and the verdict on the value stands. A membership in a set we can READ still
// earns, and a check we cannot read is still Z.   EXPECT: REFUTED, REFUTED, REFUTED, EARNED, OPEN
$p = $_GET['p'];
if (file_exists($p)) {
    include $p;
}
$q = $_GET['q'];
if (is_string($q)) {
    echo $q;
}
$parts = $_GET['parts'];
if (is_array($parts) && count($parts) > 0) {
    shell_exec('ls ' . $parts[0]);
}
$r = $_GET['r'];
if (in_array($r, ['a', 'b'], true)) {
    unlink('/srv/' . $r);
}
$s = $_GET['s'];
if (their_own_check($s)) {
    unlink('/srv/' . $s);
}
