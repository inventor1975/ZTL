<?php
// A REMOVING FILTER IS READ BY WHAT IT LEAVES. MEASURED on PHP 8.3.6: FILTER_SANITIZE_EMAIL takes the
// double quote, the angle brackets, the slash, the backslash, the space and the newline out — "</script>"
// comes back "script" — and LEAVES the single quote, the ampersand, the equals sign and the backtick.
// So it substitutes in body text and in a double-quoted attribute, and in no position a single quote
// closes: not a single-quoted attribute, not SQL inside quotes. FILTER_SANITIZE_URL is not a substitution
// at all — measured, it removes only the space and the newline.
// EXPECT: EARNED, EARNED, REFUTED, REFUTED, REFUTED
$x = $_GET['x'];
echo '<p>' . filter_var($x, FILTER_SANITIZE_EMAIL) . '</p>';
echo '<input value="' . filter_var($x, FILTER_SANITIZE_EMAIL) . '">';
echo "<input value='" . filter_var($x, FILTER_SANITIZE_EMAIL) . "'>";
mysqli_query($db, "SELECT * FROM t WHERE a = '" . filter_var($x, FILTER_SANITIZE_EMAIL) . "'");
echo '<p>' . filter_var($x, FILTER_SANITIZE_URL) . '</p>';
