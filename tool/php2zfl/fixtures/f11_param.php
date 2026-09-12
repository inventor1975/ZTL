<?php
// intra-procedural boundary: a parameter's origin is the caller's, not this file's.  EXPECT: OPEN
function load_post($c, $id) {
    return mysqli_query($c, "SELECT * FROM posts WHERE id = $id");
}
