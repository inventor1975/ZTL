<?php
// nothing attacker-controlled reaches either query.  EXPECT: EARNED, EARNED
$c = mysqli_connect("localhost", "u", "p", "db");
mysqli_query($c, "SELECT * FROM posts WHERE id = 1");
$q = "SELECT * FROM " . TABLES_PREFIX . "_posts ORDER BY id";
mysqli_query($c, $q);
