<?php
// the query lives in a method; the RAW value comes from the caller.  EXPECT: REFUTED (at the call site), and the standalone reading is not double-counted
class CPosts {
    function load($c, $id) {
        return mysqli_query($c, "SELECT * FROM posts WHERE id = $id");
    }
    function page($c) {
        return $this->load($c, $_GET['id']);
    }
}
