<?php
// a helper returns request data; the caller queries with it.  EXPECT: REFUTED
function param($name) {
    return isset($_POST[$name]) ? trim($_POST[$name]) : '';
}
$c = mysqli_connect("localhost", "u", "p", "db");
$n = param('name');
mysqli_query($c, "SELECT * FROM users WHERE name = '$n'");
