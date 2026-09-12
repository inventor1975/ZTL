<?php
// $_FILES: the browser chooses `name` and `type`; PHP writes `tmp_name`, `size`, `error`.
// EXPECT: EARNED, REFUTED
$h = fopen($_FILES['up']['tmp_name'], 'rb');
$n = fopen("/var/up/" . $_FILES['up']['name'], 'rb');
