<?php
// A SINK THAT IS NOT DECLARED IS INVISIBLE TO EVERY BENCHMARK WE HOLD — SARD plants only the families its
// generator knows, fixbench sees only what a developer fixed, the census counts what we look for. Measured
// 2026-09-10 across the four corpora: mkdir 218 calls, rename 205, copy 190, glob 71, scandir 62,
// getimagesize 57, move_uploaded_file 26, mail 26 — not one of them a sink for us until now.
// And one call can carry the danger in SEVERAL arguments: mail() folds to, subject and the extra headers
// into the message headers; copy() and rename() are two paths, not one. Judging only the first hid the rest.
// EXPECT: REFUTED, REFUTED, REFUTED, REFUTED, REFUTED, EARNED, OPEN, EARNED
$x = $_GET['x'];
mail('a@b.c', 'hello', 'body', "From: " . $x);          // the classic: CRLF in the extra headers
mail($x, 'hello', 'body');                               // the recipient reaches the To: header too
copy('/tmp/a', '/var/www/' . $x);                        // the DESTINATION is the second argument
rename('/tmp/a', '/var/www/' . $x);
scandir('/var/data/' . $x);                              // listing a directory chosen by the request
mail('a@b.c', 'hello', $x);                              // the BODY is not a header — nothing to inject
copy('/tmp/' . urlencode($x), '/var/www/fixed');         // URL-encoded is a NARROWING for a path, not a substitution
copy('/tmp/' . basename($x), '/var/www/fixed');          // basename IS the substitution for a path
