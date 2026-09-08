<?php
// header: a Location built from the request; rawurlencode substitutes for the header context.  EXPECT: REFUTED, EARNED
header("Location: " . $_GET['next']);
header("Location: /search?q=" . rawurlencode($_GET['q']));
