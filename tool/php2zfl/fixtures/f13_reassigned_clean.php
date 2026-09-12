<?php
// flow-sensitivity: the tainted value is overwritten by a constant before the sink.  EXPECT: EARNED
$c = mysqli_connect("localhost", "u", "p", "db");
$id = $_GET['id'];
$id = 7;
mysqli_query($c, "SELECT * FROM posts WHERE id = $id");
