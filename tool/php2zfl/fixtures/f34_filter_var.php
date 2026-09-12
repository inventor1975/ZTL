<?php
// filter_var with a VALIDATE filter returns a typed value or false.  EXPECT: EARNED
$c = mysqli_connect("localhost", "u", "p", "db");
$id = filter_var($_GET['id'], FILTER_VALIDATE_INT);
mysqli_query($c, "SELECT * FROM posts WHERE id = $id");
