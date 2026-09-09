<?php
function xc_clean($s) { return preg_replace('/[^a-z0-9]/', '', $s); }   // one definition confines the value
