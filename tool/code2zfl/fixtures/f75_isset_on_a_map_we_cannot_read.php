<?php
// A MAP WE CANNOT READ IS STILL A MAP. `isset($beanList[$module])` gates SuiteCRM's
// `require_once('modules/'.$module.'/TreeData.php')` on a list built by an include — a whitelist whose
// contents are invisible here, which is Z with the checker named, not the absence of a check. Its twin
// `array_key_exists($x, $map)` has answered exactly that since the guard work; the two spellings of one
// act disagreed. A map we CAN read still earns, and no check at all still refutes.
// EXPECT: OPEN, EARNED, REFUTED
$m = $_REQUEST['module'];
if (isset($beanList[$m])) {
    unlink('modules/' . $m . '/a.php');
}
$fixed = ['x' => 1, 'y' => 2];
if (isset($fixed[$m])) {
    unlink('modules/' . $m . '/b.php');
}
unlink('modules/' . $_REQUEST['other'] . '/c.php');
