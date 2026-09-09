<?php
// The parent, in its own file: it holds the sanitizer the child relies on.
class XiBase {
    protected function clean($s) { return preg_replace('/[^a-z0-9]/', '', $s); }
    protected function raw($s) { return $s; }
}
