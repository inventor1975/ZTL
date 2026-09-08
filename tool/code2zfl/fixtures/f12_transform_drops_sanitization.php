<?php
// PLANTED: substr of an escaped string can end in a lone backslash — sanitization does not survive a transformation.  EXPECT: REFUTED
$c = mysqli_connect("localhost", "u", "p", "db");
$n = substr(mysqli_real_escape_string($c, $_POST['name']), 0, 10);
mysqli_query($c, "SELECT * FROM users WHERE name = '$n'");
