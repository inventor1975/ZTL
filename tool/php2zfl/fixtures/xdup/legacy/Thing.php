<?php
// A SECOND COPY OF THE SAME CLASS, left in the tree. Only one of the two can be loaded, and this file's
// own text does not say which. The verdict here is about the code as written; whether this code RUNS is a
// separate question, and the ledger has to say that it did not answer it.
namespace Dup;
class Thing {
    public function run($db) {
        $db->query("SELECT * FROM t WHERE a = '" . $_GET['a'] . "'");
    }
}
