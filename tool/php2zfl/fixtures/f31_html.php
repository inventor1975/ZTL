<?php
// html: raw echo is an injection; htmlspecialchars substitutes; addslashes is not an HTML escaper.  EXPECT: REFUTED, EARNED, REFUTED
echo "<p>" . $_GET['name'] . "</p>";
echo "<p>" . htmlspecialchars($_GET['name']) . "</p>";
echo "<p>" . addslashes($_GET['name']) . "</p>";
