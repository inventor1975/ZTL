<?php
// $_FILES: tmp_name, size and error are written by PHP; name and type by the client.  EXPECT: EARNED, REFUTED
$data = file_get_contents($_FILES['up']['tmp_name']);
unlink("/srv/uploads/" . $_FILES['up']['name']);
