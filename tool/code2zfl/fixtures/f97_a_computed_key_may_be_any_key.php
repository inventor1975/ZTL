<?php
// f97 (2026-09-11): EXPECT L5 REFUTED (a computed key may be 'a'), L8 EARNED (another literal key only), L11 EARNED (a literal write after the computed one), L17 REFUTED (the same for a property)
$r1 = []; $r1['a'] = 'c';
$r1[$_GET['k']] = $_GET['v'];
echo $r1['a'];
$r2 = []; $r2['a'] = 'c';
$r2['b'] = $_GET['v'];
echo $r2['a'];
$r3 = []; $r3[$_GET['k']] = $_GET['v'];
$r3['a'] = 'c';
echo $r3['a'];
class K97 {
    public $f = [];
    public function run() {
        $this->f['a'] = 'c';
        $this->f[$_GET['k']] = $_GET['v'];
        echo $this->f['a'];
    }
}
