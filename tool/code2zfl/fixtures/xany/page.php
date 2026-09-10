<?php
// EXPECT: L4 REFUTED (request data carried through wrap13), L5 EARNED (esc13 substitutes it for html),
// L6 EARNED (constants only). Before the fix all three said "constants only".
echo wrap13($_GET['t']);
echo esc13($_GET['t']);
echo wrap13('Hello');
