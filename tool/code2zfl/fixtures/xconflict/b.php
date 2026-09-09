<?php
function xc_clean($s) { return $s; }                                     // the other passes it through
class XcA {
    public function safe($s) { return intval($s); }
    public function run() {
        global $db;
        $db->query("SELECT * FROM t WHERE id = " . $db->safe($_GET['x']));   // $db is not XcA: XcA::safe must not be credited
    }
}
