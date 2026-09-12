<?php
// EXPECT (this file): OPEN — two files define xc_clean() differently, so the name is a conflict and reads as unknown
require 'a.php'; require 'b.php';
mysqli_query($c, "SELECT * FROM u WHERE n = '" . xc_clean($_GET['n']) . "'");
