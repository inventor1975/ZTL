<?php
// PLANTED: a class name built from the request is instantiated.  EXPECT: REFUTED
$classname = "C" . ucfirst($_GET['name']);
$module = new $classname();
