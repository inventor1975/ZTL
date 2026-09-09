<?php
// Membership in a FIXED set is an act of checking. Against a list we cannot read it is neither a
// check nor its absence: the honest answer is Z, so the verdict is OPEN and names the list.
// (Changed 2026-09-09: this used to be REFUTED, which asserted that an unread list does not
// protect — the same over-claim we refuse for an unread function.)  EXPECT: EARNED, OPEN
$m = $_GET['module'];
if (in_array($m, array("posts", "pages", "users"))) {
    include("/srv/modules/" . $m . ".php");
}
$k = $_GET['kind'];
if (in_array($k, $allowed_kinds)) {
    include("/srv/kinds/" . $k . ".php");
}
