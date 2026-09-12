<?php
// WRITING ONE KEY DOES NOT TAINT THE OTHERS. `$this->cfg['host'] = $_SERVER['HTTP_HOST']` used to be
// joined into the whole property, so `$this->cfg['theme']` — a literal written two lines away — read as
// attacker-controlled. Reading the property AS A WHOLE must still see the tainted element, and a write
// at a COMPUTED key must taint the whole property, because we do not know which element it was.
// EXPECT: EARNED, REFUTED, REFUTED, REFUTED
class F70Cfg
{
    private $cfg;

    public function run()
    {
        $this->cfg['host'] = $_SERVER['HTTP_HOST'];
        $this->cfg['theme'] = 'default';
        unlink('/srv/' . $this->cfg['theme']);
        unlink('/srv/' . $this->cfg['host']);
        unlink('/srv/' . implode('', $this->cfg));
    }

    public function computed($k)
    {
        $this->other[$k] = $_GET['v'];
        unlink('/srv/' . $this->other['anything']);
    }
}
