<?php
// two objects share a method NAME: $db->escape is for SQL, $out->escape is for HTML (overlay-wrapper.json).  EXPECT: EARNED, REFUTED
$p = $_GET['post'];
$row = $db->query("SELECT * FROM posts WHERE alias = '" . $db->escape($p) . "'");
$row = $db->query("SELECT * FROM posts WHERE alias = '" . $out->escape($p) . "'");
