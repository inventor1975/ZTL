<?php
// A URL-encoded value in a file/URL sink is neither traversal nor proof: the scheme and host are
// literal here, but we do not read where the literal came from. Z, with the encoder named.
// Shape from wp-slimstat.php:1567.  EXPECT: OPEN, REFUTED
$r = "http://api.example.com/u?x=" . urlencode($_SERVER['REQUEST_URI']);
echo file_get_contents($r);
echo file_get_contents("/var/data/" . $_GET['f']);
