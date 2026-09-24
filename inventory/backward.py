# -*- coding: utf-8 -*-
"""The reverse pass now lives in the kernel as zbackward.py (2026-09-24), so the
studio can vendor it. This name stays for the stands and notes that cite it."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from zbackward import (backward, order, CAP_VALUE, CAP_DISPOSITION,   # noqa: E402,F401
                       MAX_K, TERMINAL)
