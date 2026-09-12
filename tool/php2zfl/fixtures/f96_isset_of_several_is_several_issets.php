<?php
// f96 (2026-09-11): EXPECT L5 OPEN (a map we cannot read, true branch), L7 EARNED (a literal map), L8 REFUTED (the negative branch establishes nothing), L9 REFUTED (the checked slot is not the one used)
$c = mysqli_connect('h', 'u', 'p', 'd');
$map = load_filters();
if (isset($_GET['v'], $_GET['f'], $map[$_GET['f']])) { mysqli_query($c, 'SELECT * FROM t WHERE ' . $_GET['f'] . ' = 1'); }
$lit = ['a' => 1, 'b' => 2];
if (isset($_GET['v'], $lit[$_GET['g']])) { mysqli_query($c, 'SELECT * FROM t WHERE ' . $_GET['g'] . ' = 1'); }
if (!isset($_GET['v'], $lit[$_GET['h']])) { mysqli_query($c, 'SELECT * FROM t WHERE ' . $_GET['h'] . ' = 1'); }
if (isset($_GET['v'], $lit[$_GET['k']])) { mysqli_query($c, 'SELECT * FROM t WHERE ' . $_GET['j'] . ' = 1'); }
