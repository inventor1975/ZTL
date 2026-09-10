<?php
// A PROPERTY THE FRAMEWORK FIXES IS NOT A LAUNDRY. The overlay may declare that `$fixdb->prefix` holds a
// value the framework confines — that is a reading of somebody else's source, quoted in the overlay — and
// then it stops being a boundary of its own. It settles ITSELF and nothing standing next to it: a request
// value concatenated with it is exactly as attacker-controlled as before, and an UNdeclared property is
// still a boundary. Written 2026-09-10, after the declaration turned user-role-editor's
// `ure_has_administrator_role` from OPEN into the developer's own `is_numeric` fix.
// EXPECT: EARNED, REFUTED, OPEN
$db->query("SELECT * FROM " . $fixdb->prefix . "users WHERE id = 1");
$db->query("SELECT * FROM " . $fixdb->prefix . "users WHERE name = '" . $_GET['n'] . "'");
$db->query("SELECT * FROM " . $other->prefix . "users WHERE id = 1");
