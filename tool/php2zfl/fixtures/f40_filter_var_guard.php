<?php
// filter_var(..., FILTER_VALIDATE_INT) in a condition is an act of checking; filter_input with the same flag is a
// substituted source; FILTER_VALIDATE_EMAIL lets a quote through; FILTER_SANITIZE_FULL_SPECIAL_CHARS is htmlspecialchars
// (html, not sql).  EXPECT: EARNED, EARNED, REFUTED, EARNED, REFUTED
$id = $_GET['id'];
if (filter_var($id, FILTER_VALIDATE_INT)) {
    $db->query("SELECT * FROM posts WHERE id = " . $id);
}
$n = filter_input(INPUT_GET, 'n', FILTER_VALIDATE_INT);
$db->query("SELECT * FROM posts WHERE n = " . $n);
$e = $_GET['e'];
if (filter_var($e, FILTER_VALIDATE_EMAIL)) {
    $db->query("SELECT * FROM users WHERE email = '" . $e . "'");
}
$c = filter_var($_GET['c'], FILTER_SANITIZE_FULL_SPECIAL_CHARS);
echo "<p>" . $c . "</p>";
$db->query("SELECT * FROM posts WHERE c = '" . $c . "'");
