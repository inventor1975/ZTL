<?php
// base64_encode confines its output to a fixed alphabet; strtr with a plain literal replacement keeps that; a replacement
// carrying a quote does not.  EXPECT: EARNED, EARNED, REFUTED
$r = $_SERVER['HTTP_REFERER'];
echo "<script src='/x?ref=" . base64_encode($r) . "'></script>";
echo "<script src='/x?ref=" . strtr(base64_encode($r), '+/=', '-_,') . "'></script>";
echo "<script src='/x?ref=" . str_replace('a', "'", base64_encode($r)) . "'></script>";
