<?php
// The other half of the collision: same class name, the other parent, and its `feed` substitutes nothing.
// EXPECT (this file): REFUTED
require 'baseb.php';
class XaDup extends XaWriterBase {
    public function run($db) {
        mysqli_query($db, "SELECT * FROM t WHERE b = '" . $this->feed($_GET['b']) . "'");
    }
}
