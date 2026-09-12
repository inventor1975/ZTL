<?php
// A check this file cannot read is not the absence of a check: the value is UNVERIFIED, and the
// verdict must name whose check to go and read. Shape taken from WordPress `wp_is_jsonp_request`
// and phpMyAdmin's own validators.  EXPECT: OPEN, OPEN, REFUTED
$cb = $_GET['callback'];
if (!wp_check_jsonp_callback($cb)) {
    exit;
}
echo "/**/" . $cb . "(1)";                 // guarded by something we cannot read → OPEN

$id = $_GET['id'];
if ($validator->isSafe($id)) {
    echo "<p>" . $id . "</p>";             // same, through a method → OPEN
}

$raw = $_GET['raw'];
echo "<p>" . $raw . "</p>";                // nothing checks it at all → REFUTED
