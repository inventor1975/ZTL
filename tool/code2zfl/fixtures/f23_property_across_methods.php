<?php
// a property set from the request in one method, queried in another.  EXPECT: REFUTED
class CUsers {
    public $nick;
    function init() {
        $this->nick = $_POST['nick'];
    }
    function find($c) {
        return mysqli_query($c, "SELECT * FROM users WHERE nick = '" . $this->nick . "'");
    }
}
