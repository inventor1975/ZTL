<?php
// WHICH QUOTE AN ESCAPER ENCODES IS DECIDED BY ITS FLAGS, AND THE FLAG ARGUMENT IS A NUMBER, NOT A NAME.
// ENT_QUOTES (3) encodes both quotes, ENT_COMPAT (2) only the double one, ENT_NOQUOTES (0) neither — and a
// bare DOCTYPE flag carries quote bits of zero (ENT_XML1 = 16, ENT_HTML5 = 48), so it encodes neither either.
// Asking only "does it mention ENT_QUOTES" credits the DOUBLE-quoted attribute that the escaper does not
// close. Found on SMF Themes/default/Xml.template.php:434, `htmlspecialchars(..., ENT_XML1)` into an attribute.
// EXPECT: REFUTED, REFUTED, EARNED, EARNED, EARNED, REFUTED, EARNED
$x = $_GET['x'];
echo '<input value="' . htmlspecialchars($x, ENT_NOQUOTES) . '">';
echo '<input value="' . htmlspecialchars($x, ENT_XML1) . '">';
echo '<input value="' . htmlspecialchars($x, ENT_COMPAT) . '">';
echo "<input value='" . htmlspecialchars($x, ENT_QUOTES) . "'>";
echo '<p>' . htmlspecialchars($x, ENT_NOQUOTES) . '</p>';
echo '<input value="' . htmlspecialchars($x, ENT_NOQUOTES | ENT_HTML5) . '">';
echo "<input value='" . htmlspecialchars($x, ENT_QUOTES | ENT_XML1) . "'>";
