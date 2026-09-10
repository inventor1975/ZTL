<?php
// WHAT A WORDPRESS SANITIZER ACTUALLY GUARANTEES, read from its own source rather than from its name.
// `sanitize_text_field` sends anything holding '<' through wp_pre_kses_less_than (a '<' with no '>' after
// it is esc_html'd) and then wp_strip_all_tags (strip_tags plus the <script>/<style> bodies), so no raw
// '<' survives. It does NOT touch quotes. Body text only: an attribute of either kind stays open, and so
// does a quoted SQL string. The name says "sanitize"; the source says how far.
// EXPECT: EARNED, REFUTED, REFUTED, REFUTED
$x = $_GET['x'];
echo '<p>' . sanitize_text_field($x) . '</p>';
echo '<input value="' . sanitize_text_field($x) . '">';
echo "<input value='" . sanitize_text_field($x) . "'>";
$wpdb->query("SELECT * FROM t WHERE a = '" . sanitize_text_field($x) . "'");
