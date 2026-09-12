<?php
// DVWA exec/impossible: is_numeric on each ELEMENT of an exploded value guards the element.  EXPECT: EARNED, REFUTED
$target = $_REQUEST['ip'];
$octet = explode(".", $target);
if (is_numeric($octet[0]) && is_numeric($octet[1]) && is_numeric($octet[2]) && is_numeric($octet[3]) && sizeof($octet) == 4) {
    $t = $octet[0] . '.' . $octet[1] . '.' . $octet[2] . '.' . $octet[3];
    shell_exec('ping -c 4 ' . $t);
}
shell_exec('ping -c 4 ' . $target);
