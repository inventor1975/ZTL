<?php
// The Writer side: same method name, and it passes the value through untouched.
class XaWriterBase {
    protected function feed($s) { return $s; }
}
