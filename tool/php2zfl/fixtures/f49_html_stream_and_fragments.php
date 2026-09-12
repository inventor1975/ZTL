<p><?= htmlspecialchars($_GET['a']) ?></p>
<a href="<?= htmlspecialchars($_GET['u']) ?>">x</a>
<?php
// the output stream (inline HTML + echoes) is lexed in order; a fragment built earlier is read where it is embedded.
// EXPECT: EARNED, REFUTED, REFUTED, EARNED
$frag = "<div id=" . $_GET['i'] . ">";
echo $frag;
$attr = " title='" . htmlspecialchars($_GET['t'], ENT_QUOTES) . "'";
echo "<span" . $attr . ">";
