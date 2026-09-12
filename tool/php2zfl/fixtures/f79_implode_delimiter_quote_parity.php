<?php
// A DELIMITER WITH QUOTES IS SAFE WHEN IT HAS AN EVEN NUMBER OF EACH: it closes one literal and opens
// the next, leaving the quoting state as it found it. `implode("','", $escaped)` inside `'...'` is the
// canonical SQL IN-list — WordPress core builds get_page_by_path() that way. An ODD count stands a
// quote in the middle of an element and does strand the escape, and a backslash may interact with it.
// EXPECT: EARNED, REFUTED, REFUTED
$parts = explode('/', $_GET['p']);
$escaped = array_map('wrap_escape', $parts);
$ok = "'" . implode("','", $escaped) . "'";
mysqli_query($db, "SELECT * FROM t WHERE a IN (" . $ok . ")");
$bad = "'" . implode("'", $escaped) . "'";
mysqli_query($db, "SELECT * FROM t WHERE b IN (" . $bad . ")");
$raw = "'" . implode("','", $parts) . "'";
mysqli_query($db, "SELECT * FROM t WHERE c IN (" . $raw . ")");
