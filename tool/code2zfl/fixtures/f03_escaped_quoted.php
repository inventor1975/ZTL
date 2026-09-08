<?php
// escaped AND inside quotes.  EXPECT: EARNED
$c = mysqli_connect("localhost", "u", "p", "db");
$n = mysqli_real_escape_string($c, $_POST['name']);
mysqli_query($c, "SELECT * FROM users WHERE name = '$n' LIMIT 1");
