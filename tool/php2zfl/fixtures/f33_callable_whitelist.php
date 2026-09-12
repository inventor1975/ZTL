<?php
// a class name from the request, verified against a fixed set, or fixed by a literal switch case.  EXPECT: EARNED, EARNED, REFUTED
$m = $_GET['m'];
if (in_array($m, ["CPosts", "CPages"], true)) {
    $obj = new $m();
}
switch ($m) {
    case "CUsers":
        $obj = new $m();
        break;
}
$n = $_GET['n'];
$obj = new $n();
