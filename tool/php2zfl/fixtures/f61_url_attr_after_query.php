<?php
// In a URL attribute the scheme is what makes a value dangerous. At the START only URL-encoding
// helps; AFTER a literal that already fixed the scheme (a path, a `?`, a `#`) ordinary HTML
// escaping is the right substitution. Shape from WordPress network/sites.php:115.
// EXPECT: EARNED, REFUTED, EARNED
$a = $_GET['a'];
echo '<form action="sites.php?action=' . htmlspecialchars($a, ENT_QUOTES) . '">';
echo '<a href="' . htmlspecialchars($a, ENT_QUOTES) . '">x</a>';
echo '<a href="' . rawurlencode($a) . '">y</a>';
