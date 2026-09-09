<?php
// an output whose position in the markup cannot be read (a standalone function body; paths that leave the lexer in
// different states) is judged as body text and SAYS SO — the status quo, named, not a stricter guess.
// EXPECT: EARNED, EARNED, EARNED, EARNED
function render() { echo htmlspecialchars($_GET['z']); }
if ($_GET['c']) {
    echo "<div";
} else {
    echo "<p>";
}
echo htmlspecialchars($_GET['y']);
