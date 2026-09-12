<?php
// f90: a check that a request slot equals a literal holds INSIDE the branch it controls, not after it.
// Found 2026-09-10 against Psalm on SuiteCRM (modules/Campaigns/WizardMarketing.php:789): a guard on a
// superglobal slot was kept in a file-wide map, so a later read anywhere in the file was credited — a
// false EARNED, the one class of answer the instrument promises never to give.
if ($_REQUEST['f'] == 'a') {
    echo '<p>' . $_REQUEST['f'] . '</p>';       // EARNED: inside the branch the value is the literal
}
echo '<p>' . $_REQUEST['f'] . '</p>';           // REFUTED: after the branch the check no longer holds
if ($_GET['g'] != 'b') {
    exit;
}
echo '<p>' . $_GET['g'] . '</p>';               // EARNED: the other path left, so the check dominates
$x = ($_POST['p'] == 'c') ? $_POST['p'] : 'd';
echo '<p>' . $x . '</p>';                       // EARNED: each branch of the ternary is a literal
echo '<p>' . $_POST['p'] . '</p>';              // REFUTED: the ternary's check does not outlive the ternary
