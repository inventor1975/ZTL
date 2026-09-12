<?php
// PLANTED: an HTML escaper used before an SQL sink.  EXPECT: REFUTED
$c = mysqli_connect("localhost", "u", "p", "db");
$n = htmlspecialchars($_POST['name']);
mysqli_query($c, "SELECT * FROM users WHERE name = '$n'");
