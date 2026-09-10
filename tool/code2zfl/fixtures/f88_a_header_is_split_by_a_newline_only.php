<?php
// A HEADER IS SPLIT BY A NEWLINE AND BY NOTHING ELSE, and that is a WEAKER requirement than the one a URL
// attribute makes. Our `header` key means URL-ENCODED, and the same key is what `href="…"` requires — so a
// substitution that only removes CR and LF must not be given it, or `javascript:` walks into every link.
// `sanitize_text_field` collapses [\r\n\t ]+ into one space (wp-includes/formatting.php): enough for a
// cookie, useless for a URL attribute, and useless for an attribute of any kind since quotes survive.
// `sanitize_textarea_field` is the same core with keep_newlines=true — the newline SURVIVES, so not even
// the cookie. Runs under overlays/wordpress.json.
// EXPECT: EARNED, REFUTED, REFUTED, REFUTED, REFUTED, EARNED
$x = $_GET['x'];
setcookie('a', sanitize_text_field($x));
setcookie('b', sanitize_textarea_field($x));
echo '<a href="' . sanitize_text_field($x) . '">go</a>';        // the scheme is NOT fixed: javascript: fits
echo '<a href="/go?u=' . sanitize_text_field($x) . '">go</a>'; // the literal fixed the scheme: an ordinary attribute
echo '<input value="' . sanitize_text_field($x) . '">';
echo '<p>' . sanitize_text_field($x) . '</p>';
