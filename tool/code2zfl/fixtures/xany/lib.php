<?php
// xany (2026-09-11): thirteen parameters, past the per-parameter limit, so pass 1 probes them all at once and the
// summary says passes ["any"]. The judge must carry the arguments through "any", not drop them as constants.
function wrap13($s, $a = 0, $b = 0, $c = 0, $d = 0, $e = 0, $f = 0, $g = 0, $h = 0, $i = 0, $j = 0, $k = 0, $l = 0) { return '<b>' . $s . '</b>'; }
function esc13($s, $a = 0, $b = 0, $c = 0, $d = 0, $e = 0, $f = 0, $g = 0, $h = 0, $i = 0, $j = 0, $k = 0, $l = 0) { return htmlspecialchars($s, ENT_QUOTES); }
