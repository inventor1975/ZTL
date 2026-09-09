<?php
// inside <script> a JavaScript encoder substitutes: json_encode with the JSON_HEX_* flags, Laravel's Js::from (overlay);
// plain json_encode does not (</script> survives it).  EXPECT: EARNED, REFUTED, EARNED
$x = $_GET['x'];
echo "<script>var a = " . json_encode($x, JSON_HEX_TAG | JSON_HEX_APOS | JSON_HEX_QUOT | JSON_HEX_AMP) . ";</script>";
echo "<script>var b = " . json_encode($x) . ";</script>";
echo "<script>var c = " . Js::from($x) . ";</script>";
