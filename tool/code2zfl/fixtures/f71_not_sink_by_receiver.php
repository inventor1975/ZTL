<?php
// `not_sinks` NAMES AN ACT, AND THE RECEIVER IS PART OF IT. WordPress's $wp_the_query->query($vars)
// takes an array of query vars, not SQL (class-wp-query.php:3983 hands it to wp_parse_args and builds
// the statement with $wpdb->prepare) — but its bare name matched the base catalog's generic `query`
// sink. Subtracting by bare name could not say this without also unsaying $db->query.
// EXPECT: REFUTED
$x = $_GET['x'];
$bound->query("SELECT * FROM t WHERE a = " . $x);
$db->query("SELECT * FROM t WHERE a = " . $x);
