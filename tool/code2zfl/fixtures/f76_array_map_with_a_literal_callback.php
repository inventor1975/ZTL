<?php
// `array_map('intval', $ids)` APPLIES intval TO EVERY ELEMENT, so the whole array carries that
// substitution — and `array_map('intval', (array) $_POST['id'])` before `IN ('".implode("','",$ids)."')`
// is how a safe list is ordinarily built. A callback whose value argument is NOT the first is not being
// used as the catalog describes (the element would arrive as the connection), so it is an unknown call.
// A callback we cannot read at all stays what it was.
// EXPECT: EARNED, EARNED, OPEN, REFUTED, REFUTED
$ids = array_map('intval', (array) $_POST['id']);
mysqli_query($db, "UPDATE t SET a = 1 WHERE id IN ('" . implode("','", $ids) . "')");
$e = array_map('mysqli_real_escape_string', (array) $_POST['e']);
mysqli_query($db, "SELECT * FROM t WHERE b = '" . $e[0] . "'");
$raw = array_map('trim', (array) $_POST['r']);
mysqli_query($db, "SELECT * FROM t WHERE c = " . $raw[0]);
$dyn = array_map($_POST['fn'], (array) $_POST['z']);
