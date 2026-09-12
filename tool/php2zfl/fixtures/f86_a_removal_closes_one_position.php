<?php
// A REMOVAL CLOSES ONE POSITION AND SAYS NOTHING ABOUT THE OTHERS. Taking the single quote out of a value
// settles a single-quoted attribute — nothing can close it — and settles nothing in body text, where `<`
// still opens a tag. Our level ladder treats `html-sq` as covering everything weaker, which is true of
// htmlspecialchars(ENT_QUOTES) and false of a removal, so removals get position-exact keys of their own.
// Only SINGLE characters count: removing a phrase leaves every character of it behind.
// Measured 2026-09-10 on SARD CWE_79, where 21 such files were false alarms of ours.
// EXPECT: EARNED, REFUTED, EARNED, REFUTED, EARNED, REFUTED
$x = $_GET['x'];
echo "<div id='" . preg_replace('/\'/', '', $x) . "'>a</div>";
echo '<p>' . preg_replace('/\'/', '', $x) . '</p>';
echo '<div id="' . str_replace('"', '', $x) . '">b</div>';
echo "<div id='" . str_replace('"', '', $x) . "'>c</div>";
echo '<p>' . str_replace(array('<', '>'), '', $x) . '</p>';
echo '<p>' . str_replace('<!-- warning -->', '', $x) . '</p>';
