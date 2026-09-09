<?php
// an object of a class defined in THIS file is followed through its own property states, in call order.
// EXPECT: REFUTED, REFUTED, REFUTED, EARNED, REFUTED
class Input {
    private $input;
    public function __construct() { $this->input = array(); $this->input['test'] = 'safe'; $this->input['real'] = $_GET['q']; }
    public function getInput() { return $this->input['real']; }
    public function direct() { return $_GET['q']; }
}
class Sanitize {
    private $data;
    public function __construct($v) { $this->data = $v; }
    public function sanitize() { $this->data = mysqli_real_escape_string($GLOBALS['conn'], $this->data); }
    public function getData() { return $this->data; }
}
$in = new Input();
$db->query("SELECT * FROM t WHERE a = '" . $in->getInput() . "'");
$db->query("SELECT * FROM t WHERE b = '" . $in->direct() . "'");
$db->query("SELECT * FROM t WHERE c = '" . (new Input())->getInput() . "'");
$s = new Sanitize($_GET['q']);
$s->sanitize();
$db->query("SELECT * FROM t WHERE d = '" . $s->getData() . "'");
$u = new Sanitize($_GET['q']);
$db->query("SELECT * FROM t WHERE e = '" . $u->getData() . "'");
$u->sanitize();
