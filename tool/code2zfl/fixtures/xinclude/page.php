<?php
// EXPECT: OPEN, EARNED, REFUTED, REFUTED — p and q come from front.php, which this file requires;
// s was checked there only inside a branch that does not leave, r was never checked.
require __DIR__ . '/front.php';
unlink('/srv/' . $_GET['p']);
unlink('/srv/' . $_GET['q']);
unlink('/srv/' . $_GET['r']);
unlink('/srv/' . $_GET['s']);
