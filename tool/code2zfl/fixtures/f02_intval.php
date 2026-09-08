<?php
// intval substitutes the value for every context.  EXPECT: EARNED
$c = mysqli_connect("localhost", "u", "p", "db");
$id = intval($_GET['id']);
mysqli_query($c, "SELECT * FROM posts WHERE id = $id");
