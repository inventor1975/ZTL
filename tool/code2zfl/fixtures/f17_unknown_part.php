<?php
// the attacker-controlled part is a number; another part comes from a DB row this file cannot vouch for.  EXPECT: OPEN
$c = mysqli_connect("localhost", "u", "p", "db");
$row = mysqli_fetch_assoc(mysqli_query($c, "SELECT * FROM groups LIMIT 1"));
$set = "";
foreach ($row as $col => $old) {
    $set .= $col . " = " . intval($_POST[$col]) . ", ";
}
mysqli_query($c, "UPDATE groups SET " . substr($set, 0, -2) . " WHERE id = 1");
