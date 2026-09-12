<?php
// EXPECT (this file): EARNED, REFUTED — the method that runs is defined in the parent, another file.
require 'base.php';
class XiChild extends XiBase {
    public function run($db) {
        mysqli_query($db, "SELECT * FROM t WHERE a = '" . $this->clean($_GET['a']) . "'");
        mysqli_query($db, "SELECT * FROM t WHERE b = '" . $this->raw($_GET['b']) . "'");
    }
}
