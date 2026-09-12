<?php
// EXPECT: L4 OPEN (request data carried through wrap13; which argument arrives raw the all-at-once probe cannot
// say), L5 EARNED (esc13 substitutes it for html), L6 EARNED (constants only). Before the fix: all three EARNED.
echo wrap13($_GET['t']);
echo esc13($_GET['t']);
echo wrap13('Hello');
