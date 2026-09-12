<?php
// The Reader side of the pair: its `feed` narrows the value to an alphabet.
class XaReaderBase {
    protected function feed($s) { return preg_replace('/[^a-z0-9]/', '', $s); }
}
