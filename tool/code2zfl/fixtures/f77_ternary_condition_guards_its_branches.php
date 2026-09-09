<?php
// A TERNARY IS AN `if`, AND ITS CONDITION GUARDS ITS BRANCHES. `$show = in_array(trim($_REQUEST['show']),
// ['all','none']) ? $_REQUEST['show'] : 'all';` is the ordinary PHP way to validate-or-default; we read
// guards only from if/elseif/while/do, so the same check written as a statement earned and written as a
// ternary refuted. The FALSE branch gets the negated guards, and a check we cannot read still gives Z.
// EXPECT: EARNED, EARNED, OPEN, REFUTED
$a = in_array(trim($_REQUEST['a']), ['all', 'none']) ? $_REQUEST['a'] : 'all';
header('Location: /x?a=' . $a);
$b = ctype_alpha($_REQUEST['b']) ? $_REQUEST['b'] : 'all';
header('Location: /x?b=' . $b);
$c = their_check($_REQUEST['c']) ? $_REQUEST['c'] : 'all';
header('Location: /x?c=' . $c);
$d = isset($_REQUEST['d']) ? $_REQUEST['d'] : 'all';
header('Location: /x?d=' . $d);
