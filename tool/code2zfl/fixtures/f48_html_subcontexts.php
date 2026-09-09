<?php
// where a value lands in the markup decides what substitutes it (atoms.php Html lexer).
// EXPECT: EARNED, EARNED, REFUTED, EARNED, REFUTED, EARNED, REFUTED, EARNED, EARNED, REFUTED, EARNED, REFUTED, REFUTED, EARNED
$x = $_GET['x'];
echo "<p>" . htmlspecialchars($x) . "</p>";                                    // body text
echo "<div title=\"" . htmlspecialchars($x) . "\">";                           // double-quoted attribute: " is encoded
echo "<div title='" . htmlspecialchars($x, ENT_COMPAT) . "'>";                 // single-quoted: ' is NOT encoded
echo "<div title='" . htmlspecialchars($x, ENT_QUOTES) . "'>";                 // single-quoted with ENT_QUOTES
echo "<div id=" . htmlspecialchars($x) . ">";                                  // unquoted: a space ends the value
echo "<div id=" . intval($x) . ">";                                            // a number needs no quotes
echo "<a href='" . htmlspecialchars($x, ENT_QUOTES) . "'>";                    // URL attribute: javascript: needs no quote
echo "<script>var a = '" . htmlspecialchars($x, ENT_QUOTES) . "';</script>";   // a quoted script string, ' encoded: stays a string
echo "<a href='?id=" . urlencode($x) . "'>";                                   // URL-encoded inside a URL attribute
echo "<button onclick=\"go('" . htmlspecialchars($x, ENT_QUOTES) . "')\">";    // event handler: entities are decoded first
echo "<script>var b = '" . htmlspecialchars($x, ENT_QUOTES) . "';</script>";          // a quoted script string: ' encoded, </script> impossible  EARNED
echo "<script>var c = '" . htmlspecialchars($x, ENT_COMPAT) . "';</script>";          // ' not encoded                                          REFUTED
echo "<script>setTimeout('" . htmlspecialchars($x, ENT_QUOTES) . "', 10);</script>"; // the string is RUN as code                             REFUTED
echo "<p>" . urlencode($x) . "</p>";                                                  // URL-encoding leaves no bracket: body text is fine     EARNED
