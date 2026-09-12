<?php
// an anchored regex over a plain character class verifies; an unanchored one does not.  EXPECT: EARNED, REFUTED
$c = mysqli_connect("localhost", "u", "p", "db");
$a = $_GET['alias'];
if (preg_match('/^[a-z0-9_-]+$/', $a)) {
    mysqli_query($c, "SELECT * FROM posts WHERE alias = '$a'");
}
$b = $_GET['word'];
if (preg_match('/[a-z]+/', $b)) {
    mysqli_query($c, "SELECT * FROM posts WHERE word = '$b'");
}
