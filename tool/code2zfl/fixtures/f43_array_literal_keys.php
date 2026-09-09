<?php
// a value written under one key is not read back under another; under the SAME key it is.  EXPECT: OPEN, REFUTED, REFUTED
$row = $db->fetch_row("SELECT * FROM opts");
$row['value'] = $_GET['v'];
unserialize($row['options']);
$db->query("UPDATE opts SET value = '" . $row['value'] . "'");
$d = array();
$d['id'] = $_GET['id'];
$d['name'] = "fixed";
$db->query("SELECT * FROM posts WHERE id = " . $d['id']);
