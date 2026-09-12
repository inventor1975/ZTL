<?php
// $_SERVER is attacker-written only in part: REMOTE_ADDR is the server's, HTTP_USER_AGENT is the client's.  EXPECT: EARNED, REFUTED
$c = mysqli_connect("localhost", "u", "p", "db");
mysqli_query($c, "INSERT INTO visits (ip) VALUES ('" . $_SERVER['REMOTE_ADDR'] . "')");
mysqli_query($c, "INSERT INTO visits (ua) VALUES ('" . $_SERVER['HTTP_USER_AGENT'] . "')");
