<?php
// the callee substitutes the parameter itself; the caller passes it raw.  EXPECT: EARNED
function load_post($c, $id) {
    $id = intval($id);
    return mysqli_query($c, "SELECT * FROM posts WHERE id = $id");
}
$c = mysqli_connect("localhost", "u", "p", "db");
load_post($c, $_GET['id']);
