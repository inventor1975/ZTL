<?php
// setcookie($name, $value): the attacker-controlled part is the SECOND argument; the first is a constant name.
// Judging the first returned EARNED on a live flaw (bWAPP xss_stored_2.php).  EXPECT: REFUTED, EARNED
$g = $_REQUEST['genre'];
setcookie("movie_genre", $g, time() + 3600, "/", "", false, false);
setcookie($g, "fixed-value", time() + 3600);
