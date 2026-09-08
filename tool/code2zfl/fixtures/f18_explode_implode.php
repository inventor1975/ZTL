<?php
// splitting on a space and joining with '%' cannot strand an escape.  EXPECT: EARNED
$c = mysqli_connect("localhost", "u", "p", "db");
$word = mysqli_real_escape_string($c, $_GET['word']);
$w = explode(" ", strtolower($word));
mysqli_query($c, "SELECT * FROM posts WHERE LOWER(name) LIKE '%" . implode("%", $w) . "%'");
