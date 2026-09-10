<?php
// ONE BARE CLASS NAME, TWO NAMESPACES, TWO PARENTS. The tree-wide `class -> parent` map is keyed by the
// bare name, so `XaDup` here and `XaDup` in writer.php collide; last-writer-wins made the winner depend on
// which BATCH the file landed in (measured 2026-09-10 on dolibarr: Reader\Csv extends BaseReader and
// Writer\Csv extends BaseWriter, and 7 sinks in Reader/Csv.php appeared at --jobs 12 and vanished at 16).
// The parent written in THIS file is not a guess about a name — it is this file's own text, and it wins.
// EXPECT (this file): EARNED
require 'basea.php';
class XaDup extends XaReaderBase {
    public function run($db) {
        mysqli_query($db, "SELECT * FROM t WHERE a = '" . $this->feed($_GET['a']) . "'");
    }
}
