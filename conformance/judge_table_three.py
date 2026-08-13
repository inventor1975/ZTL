# -*- coding: utf-8 -*-
"""
The three-quantity sweep — the same table, the other space.

Pairs prove nothing about triples: units combine, a lattice can be forced
through an intermediate, and a cure named for one quantity may be the cure
for another. This runs `judge_table` over the `three` space, which is
coarser per quantity on purpose — the full vocabulary cubed is seven million
cases, and trimming the dimensions pairs already cover exhaustively brings it
back to the size a run can afford every time.

Run:  python3 conformance/judge_table_three.py
"""
import os
import sys

os.environ.setdefault("ZTL_SPACE", "three")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import judge_table                                              # noqa: E402

if __name__ == "__main__":
    sys.exit(judge_table.main())
