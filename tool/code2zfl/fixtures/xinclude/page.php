<?php
// EXPECT: OPEN, EARNED, REFUTED — the first two facts come from front.php, which this file requires.
require __DIR__ . '/front.php';
unlink('/srv/' . $_GET['p']);
unlink('/srv/' . $_GET['q']);
unlink('/srv/' . $_GET['r']);
