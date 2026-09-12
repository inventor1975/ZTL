<?php
// an UNKNOWN call's result is not visible even over constant arguments: $o->get() reads the object's state.
// time() is on the allow-list (transparent): over constants it is a constant.  EXPECT: OPEN, EARNED
$o = new Input();
$v = $o->getInput();
$db->query("SELECT * FROM posts WHERE v = '" . $v . "'");
$db->query("SELECT * FROM posts WHERE t < " . time());
