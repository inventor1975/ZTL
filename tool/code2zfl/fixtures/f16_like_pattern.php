<?php
// inside quotes even though the literal before the value ends with '%', not with a quote.  EXPECT: EARNED
$c = mysqli_connect("localhost", "u", "p", "db");
$w = mysqli_real_escape_string($c, $_GET['q']);
mysqli_query($c, "SELECT * FROM posts WHERE name LIKE '%" . $w . "%' ORDER BY id");
