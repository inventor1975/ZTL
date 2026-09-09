<?php
// sprintf: %d SUBSTITUTES (a number comes out whatever went in); %s carries the value and the format's quotes decide.  EXPECT: EARNED, EARNED, REFUTED, REFUTED
$id = $_GET['id'];
$db->query(sprintf("SELECT * FROM posts WHERE id = %d", $id));
$db->query(sprintf("SELECT * FROM posts WHERE alias = '%s'", mysqli_real_escape_string($conn, $id)));
$db->query(sprintf("SELECT * FROM posts WHERE id = %s", mysqli_real_escape_string($conn, $id)));
$db->query(sprintf("SELECT * FROM posts WHERE alias = '%s'", $id));
