<?php
// URL-ENCODING SUBSTITUTES IN A URL, AND NOWHERE THE URL PARSER DOES NOT RUN. In an event handler the
// browser decodes entities BEFORE the script parser sees them; in a style attribute or a <script> body
// the syntax is not HTML at all; an unquoted attribute ends at a space. These positions take a whitelist
// or a numeric cast and nothing else. Written 2026-09-10 as a GUARD: renumbering the html levels made
// `header` earn in every one of these, the fixture stand stayed green, and only SARD CWE_79 caught it
// (misses 1152 -> 1632). A hole a benchmark finds and the stand does not is a hole in the stand.
// EXPECT: EARNED, REFUTED, REFUTED, REFUTED, REFUTED
$x = $_GET['x'];
echo '<a href="/s?q=' . urlencode($x) . '">go</a>';
echo '<a onclick="f(' . urlencode($x) . ')">go</a>';
echo '<div style="width:' . urlencode($x) . '">w</div>';
echo '<input value=' . urlencode($x) . '>';
echo '<script>var a = ' . urlencode($x) . ';</script>';
