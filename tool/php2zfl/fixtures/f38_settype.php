<?php
// settype($x, "integer") is a substitution BY REFERENCE: from here on $x is a number.  EXPECT: EARNED
$id = $_GET['id'];
settype($id, "integer");
$db->query("SELECT * FROM posts WHERE id = " . $id);
