<?php
// PLANTED: a Location header built from the request — header injection / open redirect.  EXPECT: REFUTED
header("Location: " . $_GET['next']);
