<?php
// PLANTED: every element of $_POST is attacker-controlled; the loop body queries with it.  EXPECT: REFUTED
$c = mysqli_connect("localhost", "u", "p", "db");
foreach ($_POST['ids'] as $id) {
    mysqli_query($c, "DELETE FROM posts WHERE id = $id");
}
