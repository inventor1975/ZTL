<?php
// `if (!check) exit;` — what follows runs only when the check held.  EXPECT: EARNED
$c = mysqli_connect("localhost", "u", "p", "db");
$id = $_GET['id'];
if (!ctype_digit($id)) {
    exit("bad id");
}
mysqli_query($c, "SELECT * FROM posts WHERE id = $id");
