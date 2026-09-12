<?php
// The callee lives in another file. Pass 1 records what it does with a tainted parameter.
function xf_db_get($id) {                                  // a SINK inside another file
    return mysqli_query($GLOBALS['c'], "SELECT * FROM t WHERE id = " . $id);
}
function xf_clean($s) {                                    // a real sanitizer
    return preg_replace('/[^a-z0-9]/', '', strtolower($s));
}
function xf_allowed($x) {                                  // a guard
    return in_array($x, ['a', 'b', 'c'], true);
}
function xf_wrap($s) {                                     // carries the taint through, unchanged
    return "[" . $s . "]";
}
