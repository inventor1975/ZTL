<?php
// A whitelist held in a once-assigned literal map is a check, exactly like a constant one.
// Shape from WordPress `_get_list_table`.  EXPECT: EARNED, REFUTED
$core = array('WP_Posts_List_Table' => 'posts', 'WP_Users_List_Table' => 'users');
$cls = $_GET['c'];
if (isset($core[$cls])) {
    $a = new $cls();
}
$other = $_GET['d'];
$b = new $other();
