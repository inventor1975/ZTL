<?php
// what was STORED — the session, a file, a process's output, an unserialized blob — is Z in the base catalog and a
// SOURCE under overlays/stored-input.json. The stand runs this file both ways.
// EXPECT (base):   OPEN, OPEN, OPEN, OPEN, OPEN        EXPECT (stored-input): REFUTED x5
$a = $_SESSION['user'];
$db->query("SELECT * FROM t WHERE a = '" . $a . "'");
$h = fopen("/tmp/tainted.txt", "r"); $b = fgets($h, 4096);
$db->query("SELECT * FROM t WHERE b = '" . $b . "'");
exec("/usr/bin/producer", $out, $rc); $c = $out[0];
$db->query("SELECT * FROM t WHERE c = '" . $c . "'");
$d = `cat /tmp/tainted.txt`;
$db->query("SELECT * FROM t WHERE d = '" . $d . "'");
$e = unserialize(file_get_contents("/var/lib/app/blob"));
$db->query("SELECT * FROM t WHERE e = '" . $e . "'");
