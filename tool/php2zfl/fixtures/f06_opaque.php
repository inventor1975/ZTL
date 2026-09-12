<?php
// the value passes through a function this file cannot see.  EXPECT: OPEN (weak links named)
$c = mysqli_connect("localhost", "u", "p", "db");
$n = clean_input($_POST['name']);
mysqli_query($c, "SELECT * FROM users WHERE name = '$n'");
