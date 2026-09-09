<?php
// A CHECK WE CANNOT READ leaves its mark on a SUPERGLOBAL ELEMENT too. A slot never lives in the
// environment — it is read straight from the source each time — so `if (their_check($_GET['a']))` had
// nowhere to leave its mark and was dropped in silence, and the sink then read as a plain refutation.
// A KNOWN guard on a slot already worked (f63); this is its unreadable twin.
// EXPECT: OPEN, OPEN, EARNED, REFUTED
if (their_check($_GET['a'])) {
    unlink('/srv/' . $_GET['a']);
}
$b = $_GET['b'];
if (their_check($b)) {
    unlink('/srv/' . $b);
}
if (ctype_alpha($_GET['c'])) {
    unlink('/srv/' . $_GET['c']);
}
unlink('/srv/' . $_GET['d']);
