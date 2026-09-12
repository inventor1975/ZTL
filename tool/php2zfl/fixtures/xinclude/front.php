<?php
// A FRONT CONTROLLER. It checks the request once; every page that requires it is judged under that
// check. `their_gate` is a name this tree does not define — an unreadable check, so the value it
// guards is Z (OPEN, checker named), never clean. `ctype_alpha` we can read, and it substitutes —
// but ONLY where it dominates: `q` is checked on the only path that goes on (the other dies); `s` is
// checked inside a branch that does not leave, so after it `s` is anything (f90, 2026-09-10: this
// fixture used to expect EARNED for such a check, i.e. it had the leak written into it).
if (!their_gate($_GET['p'])) {
    die('no');
}
if (!ctype_alpha($_GET['q'])) {
    die('no');
}
if (ctype_alpha($_GET['s'])) {
    error_log('ok');
}
