<?php
// A FRONT CONTROLLER. It checks the request once; every page that requires it is judged under that
// check. `their_gate` is a name this tree does not define — an unreadable check, so the value it
// guards is Z (OPEN, checker named), never clean. `ctype_alpha` we can read, and it substitutes.
if (!their_gate($_GET['p'])) {
    die('no');
}
if (ctype_alpha($_GET['q'])) {
    error_log('ok');
}
