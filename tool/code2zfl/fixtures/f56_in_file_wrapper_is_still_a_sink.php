<?php
// a wrapper class defined in THIS file whose method is a catalog sink: the call site is judged as the sink FIRST
// (even when the body is opaque), and the body is followed too — query2 is not a catalog sink, so only its inner
// mysqli_query is judged.  EXPECT: REFUTED, REFUTED
class DB {
    private $c;
    public function __construct() { $this->c = opaque_connect(); }
    public function query($q) { return opaque_run($this->c, $q); }          // body this file cannot read
    public function query2($q) { return mysqli_query($this->c, $q); }        // body with a real sink inside
}
$db = new DB();
$db->query("SELECT * FROM t WHERE a = '" . $_GET['a'] . "'");
$db->query2("SELECT * FROM t WHERE b = '" . $_GET['b'] . "'");
