<?php
// DVWA upload/impossible: strtolower($ext) == 'jpg' checks $ext itself — a case change cannot hide a quote.  EXPECT: EARNED, REFUTED
$name = $_FILES['f']['name'];
$ext = substr($name, strrpos($name, '.') + 1);
if (strtolower($ext) == 'jpg' || strtolower($ext) == 'png') {
    unlink("/tmp/up/" . md5($name) . "." . $ext);
}
unlink("/tmp/up/" . $ext);
