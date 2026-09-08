<?php
// a DB wrapper: ->escape substitutes for the quoted context, ->query is the sink (overlay-wrapper.json).  EXPECT: EARNED
$p = $_GET['post'];
$row = $db->query("SELECT * FROM posts WHERE alias = '" . $db->escape($p) . "'");
