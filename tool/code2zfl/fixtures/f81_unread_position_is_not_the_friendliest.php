<?php
// AN UNREAD POSITION IS NOT THE FRIENDLIEST POSITION. When the html sub-context cannot be read — a
// function body that nothing in the file calls, so the stream state on entry is any of nineteen — the
// output used to be judged as body text, and body-text escaping was credited. But
// `htmlspecialchars($x, ENT_COMPAT)` leaves the single quote alone: if the value in fact lands in
// value='…', it walks straight out. A substitution covering EVERY position still earns; one covering
// only some goes unverified with the position named.
// EXPECT: OPEN, EARNED, EARNED
function f81_compat($k)
{
    echo "<input type='text' value='" . htmlspecialchars($_POST[$k], ENT_COMPAT) . "'> ";
}
function f81_quotes($k)
{
    echo "<input type='text' value='" . htmlspecialchars($_POST[$k], ENT_QUOTES) . "'> ";
}
function f81_numeric($k)
{
    echo "<input type='text' value='" . intval($_POST[$k]) . "'> ";
}
