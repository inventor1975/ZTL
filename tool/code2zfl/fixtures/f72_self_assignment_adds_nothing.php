<?php
// `$this->p = <an expression built only from $this->p and literals>` ADDS NOTHING to the property.
// Pico writes `$this->config = is_array($this->config) ? $this->config : array();` — and because a
// property is held as a class-wide join with no order between methods, that read-and-write-back
// carried an element tainted in ANOTHER method back into the bulk, where every other key inherited it.
// EXPECT: EARNED, REFUTED
class F72Cfg
{
    private $cfg;

    public function fill()
    {
        $this->cfg['host'] = $_SERVER['HTTP_HOST'];
    }

    public function use_it()
    {
        $this->cfg = is_array($this->cfg) ? $this->cfg : array();
        $this->cfg['theme'] = 'default';
        unlink('/srv/' . $this->cfg['theme']);
        unlink('/srv/' . $this->cfg['host']);
    }
}
