<?php
// an escaped part of UNKNOWN origin outside quotes is the weak link (OPEN), not a refutation; inside quotes it is settled.  EXPECT: OPEN, EARNED
$h = mysqli_real_escape_string($conn, $_GET['h']);
$g = mysqli_real_escape_string($conn, $this->getParam('group'));
$db->query("UPDATE users SET group_id = " . $g . ", hash = '" . $h . "'");
$db->query("UPDATE users SET group_id = '" . $g . "', hash = '" . $h . "'");
