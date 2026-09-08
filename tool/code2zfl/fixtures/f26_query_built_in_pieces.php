<?php
// a query assembled from fragments: the escaped part was placed inside quotes where it was embedded, and the
// fragment then stands OUTSIDE quotes in the outer string — that is not a defect.  EXPECT: EARNED ×3
function where_name($c) {
    return "name = '" . mysqli_real_escape_string($c, $_GET['name']) . "'";
}
$c = mysqli_connect("localhost", "u", "p", "db");
$q = "SELECT * FROM users WHERE " . where_name($c);
$q .= " AND status = 1";
mysqli_query($c, $q);
$set = array();
$set[] = "nick = '" . mysqli_real_escape_string($c, $_POST['nick']) . "'";
$set[] = "age = " . intval($_POST['age']);
mysqli_query($c, "UPDATE users SET " . implode(", ", $set) . " WHERE id = 1");
$w = "id = " . intval($_GET['id']);
mysqli_query($c, "DELETE FROM users WHERE " . $w);
