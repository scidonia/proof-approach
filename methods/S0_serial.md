# S0 — serial single agent

**Question:** what does one agent achieve per wall-clock hour with no
coordination?

## Organisation

One worker, `a1`, owns the whole problem list.  It works the problems in the
order recorded in `run.json`, one at a time, and does not start the next until
the current one is green or it decides to abandon it.  Abandoning is recorded:
the worker runs `pa.py note ... --text "abandon: <reason>"` and moves on.

No supervisor, no shared workspace, no other agent reads or writes its files.

## Clock

The run starts at `pa.py start` and ends when every problem is green, when the
worker abandons the last one, or at the budget.  The scorer uses the wall clock
from `started_at` to `ended_at`, and each problem's first green event.

## What is measured

- problems solved per wall-clock hour;
- minutes per solved problem;
- agent-minutes per solved problem (equal to wall-clock minutes here);
- compile checks and failed checks per solve;
- targets proved per hour (partial credit on multi-target problems).

This is the control.  Every other method is compared on the same problem set,
budget and brief.
