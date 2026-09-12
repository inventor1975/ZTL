<?php
// PLANTED: escaped but NOT quoted — escaping without quotes protects nothing.  EXPECT: REFUTED
$c = mysqli_connect("localhost", "u", "p", "db");
$n = mysqli_real_escape_string($c, $_POST['id']);
mysqli_query($c, "SELECT * FROM users WHERE id = " . $n);
