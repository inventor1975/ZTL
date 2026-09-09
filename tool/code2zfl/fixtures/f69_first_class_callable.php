<?php
// PHP 8.1 FIRST-CLASS CALLABLE SYNTAX: `gate(...)` puts a VariadicPlaceholder where an argument would
// be. Reading it as an expression was a fatal error that killed the whole run — contao, magento2 and
// symfony, 39 000 files, judged as nothing. A placeholder is not a value and checks nothing.
// EXPECT: REFUTED
function gate($v)
{
    if ($v === 'x') {
        die('no');
    }
}
$fn = gate(...);
gate(...);
unlink('/srv/' . $_GET['a']);
