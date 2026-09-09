<?php
// EXPECT (in this file): REFUTED, EARNED, OPEN, REFUTED
require 'lib.php';
$c = mysqli_connect("localhost", "u", "p", "d");
xf_db_get($_GET['id']);                                              // sink inside the callee
mysqli_query($c, "SELECT * FROM u WHERE n = '" . xf_clean($_GET['n']) . "'");
$k = $_GET['k'];
if (xf_allowed($k)) { mysqli_query($c, "SELECT * FROM v WHERE k = '" . $k . "'"); }
mysqli_query($c, "SELECT * FROM w WHERE q = " . xf_wrap($_GET['q']));
