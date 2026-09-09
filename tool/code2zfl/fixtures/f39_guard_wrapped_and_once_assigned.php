<?php
// a guard read through `== 1` / `=== 0`, with its pattern or list in a ONCE-assigned variable, is still the guard.
// a list assigned TWICE is not a fixed set.  EXPECT: EARNED, EARNED, EARNED, REFUTED
$re = "/^[0-9]+$/";
$allowed = array("posts", "pages");
$id = $_GET['id'];
if (preg_match($re, $id) == 1) {
    $db->query("SELECT * FROM posts WHERE id = " . $id);
}
$m = $_GET['m'];
if (in_array($m, $allowed, true)) {
    include("/srv/modules/" . $m . ".php");
}
$k = $_GET['k'];
if (preg_match($re, $k) === 0) { exit; }
$db->query("SELECT * FROM posts WHERE k = " . $k);
$twice = array("a", "b");
$twice = load_list();
$t = $_GET['t'];
if (in_array($t, $twice)) {
    include("/srv/t/" . $t . ".php");
}
