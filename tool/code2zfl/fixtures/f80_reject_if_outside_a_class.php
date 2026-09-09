<?php
// REJECT-IF-CONTAINS is hand-rolled validation written the other way round. `preg_match('/[^a-z0-9]/', $x)`
// matches everything OUTSIDE a readable class, so on the path where it did NOT match, the value is confined
// to that class — the credit belongs to the FALSE branch, the mirror of an anchored positive pattern which
// credits the true one. A pattern that is not a negated class confines nothing and gets nothing, and the
// branch that DID match (the rejected one) gets nothing either.
// EXPECT: EARNED, REFUTED, REFUTED
$b = $_GET['b'];
if (preg_match('/[^a-z0-9]/', $b)) {
    exit;
}
unlink('/srv/' . $b);
$c = $_GET['c'];
if (preg_match('/bad/', $c)) {
    die('no');
}
unlink('/srv/' . $c);
$d = $_GET['d'];
if (preg_match('/[^a-z]/', $d)) {
    unlink('/srv/' . $d);
}
