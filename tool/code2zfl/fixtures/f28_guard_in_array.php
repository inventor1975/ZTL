<?php
// membership in a FIXED set is an act of checking; against an unknown list it is not.  EXPECT: EARNED, REFUTED
$m = $_GET['module'];
if (in_array($m, array("posts", "pages", "users"))) {
    include("/srv/modules/" . $m . ".php");
}
$k = $_GET['kind'];
if (in_array($k, $allowed_kinds)) {
    include("/srv/kinds/" . $k . ".php");
}
