<?php
// A whitelist whose contents come back from a call is a check we cannot read — Z, not a refutation.
// Shape from Wordfence 9.0.1 lib/wordfenceClass.php:1732.  EXPECT: OPEN, EARNED, REFUTED
$f = $_POST['action'];
$actions = self::_ajaxActions();
if (array_key_exists($f, $actions)) { $r = call_user_func('wf::ajax_' . $f); }
$g = $_POST['g'];
if (array_key_exists($g, array('a' => 1, 'b' => 2))) { $r = call_user_func('wf::ajax_' . $g); }
$h = $_POST['h'];
$r = call_user_func('wf::ajax_' . $h);
