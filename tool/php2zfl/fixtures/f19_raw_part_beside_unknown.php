<?php
// PLANTED: the attacker part reaches the include unsubstituted; the template name beside it is unknown — that cannot help.  EXPECT: REFUTED
$path = "/srv/tpl/" . $settings->template . "/index-" . str_replace("..", "", $_REQUEST['module']) . ".html.php";
include($path);
