<?php
// The copy that the application loads. Its query is built with a substitution.
namespace Dup;
class Thing {
    public function run($db) {
        $db->query("SELECT * FROM t WHERE a = '" . wrap_escape($_GET['a']) . "'");
    }
}
