<?php
// PLANTED: one branch sanitizes, the other does not — the unsanitized path exists.  EXPECT: REFUTED
$c = mysqli_connect("localhost", "u", "p", "db");
if (isset($_GET['strict'])) {
    $id = intval($_GET['id']);
} else {
    $id = $_GET['id'];
}
mysqli_query($c, "SELECT * FROM posts WHERE id = $id");
