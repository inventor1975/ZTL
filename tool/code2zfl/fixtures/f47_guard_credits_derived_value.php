<?php
// DVWA upload/impossible: the path is built from the extension BEFORE the extension is checked. The check is credited to
// the derived path because its only tainted parent is the extension. NOT credited when the derived value also carries
// another element ($octet[1] unchecked), nor when the checked variable was reassigned from elsewhere.  EXPECT: EARNED, REFUTED, REFUTED
$name = $_FILES['f']['name'];
$ext = substr($name, strrpos($name, '.') + 1);
$random = bin2hex(random_bytes(16)) . '.' . $ext;
$tmp = sys_get_temp_dir();
$tmp .= DIRECTORY_SEPARATOR . $random;
if (strtolower($ext) == 'jpg' || strtolower($ext) == 'png') {
    unlink($tmp);
}
$octet = explode(".", $_GET['ip']);
$pair = $octet[0] . '.' . $octet[1];
if (is_numeric($octet[0])) {
    shell_exec('ping ' . $pair);
}
$a = $_GET['a'];
$path = "/srv/" . $a;
$a = $_GET['b'];
if (ctype_alpha($a)) {
    unlink($path);
}
