<?php
// PLANTED: attacker-controlled id reaches the query with no substitution.  EXPECT: REFUTED
$c = mysqli_connect("localhost", "u", "p", "db");
$id = $_GET['id'];
mysqli_query($c, "SELECT * FROM posts WHERE id = $id");
