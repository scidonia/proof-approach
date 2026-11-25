# S4 — large blind swarm of eight

**Question:** does doubling the blind swarm's size double the throughput, or
does contention eat the gain?

## Organisation

Eight workers, `a1`–`a8`, each with an isolated workspace, racing exactly as
S1 does.  No communication, no shared board in use.  Problems are raced in the
same order as S1.

## Why this is a clean doubling test

S1 and S4 use the same brief, the same statements, the same budget and the
same stopping rule.  The only difference is worker count.  On an eight-core
host, eight simultaneous elaborations also contend for CPU and memory, so the
result measures the *deployed* rate, not an idealised one.

## What is measured

- problems per wall-clock hour against S1's rate;
- agent-minutes per solve;
- **efficiency ratio**: solve rate at eight workers divided by solve rate at
  four, per tier;
- contention: check wall time at eight workers against the same check at one
  (the harness records every check's duration), and the number of checks killed
  by the memory ceiling.

If the ratio is below about 1.4, the marginal agent is buying less than its
cost and the bottleneck is somewhere other than worker count.
