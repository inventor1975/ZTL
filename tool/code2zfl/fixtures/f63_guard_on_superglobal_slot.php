<?php
// A guard on a superglobal ELEMENT has no variable to mark, and used to count for nothing.
// Shape from events-manager 7.4.3 admin/em-options.php:462.  EXPECT: EARNED, REFUTED
if (preg_match('/^[a-zA-Z_0-9]+$/', $_REQUEST['option_name'])) {
    $r = call_user_func("EM_Formats::" . $_REQUEST['option_name'], '');
}
$s = call_user_func("EM_Formats::" . $_REQUEST['other'], '');
