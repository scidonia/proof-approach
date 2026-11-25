# Proof throughput: index and speedup

Results from the first pilot block of `proof-approach`.  Each cell is the
**time to the first green check** for a fixed Lean problem, under one
organisation.  The slowest organisation on a problem is the index base, so
**100 = slowest** and lower is faster.

## Definitions

For a problem with method times `t_m` and slowest time `t_max`:

```
index(m)  = 100 × t_m / t_max        # 100 is slowest, lower is faster
speedup(m) = t_max / t_m             # how many times faster than the slowest
```

`agent-min` is the allocated agent time for the solve:
`agents × solve time / 60`.  It is the cost side of the speedup.

The index is **per problem**: an index of 40 on `gcd` and an index of 40 on
`stlc` mean the same relative position, not the same absolute time.

## Methods

| id | agents | organisation |
| --- | ---: | --- |
| S0 | 1 | serial, no coordination |
| S1 | 4 | blind race, isolated workspaces |
| S2 | 5 | 4 workers + cross-talk supervisor (verified checkpoints broadcast) |
| S3 | 5 | 4 workers + lemma-cutting supervisor (plan, assign, integrate) |
| S4 | 8 | blind race, isolated workspaces |

## Per-problem index

### `easy/gcd` — 2 targets

S0 and S1 are means of two clean runs; S2–S4 are single runs.  The slowest is
S3 at 326.2 s, so S3 is the 100 line.

| method | time s | index | speedup | agent-min |
| --- | ---: | ---: | ---: | ---: |
| S4 | 72.2 | **22.1** | **4.52×** | 9.6 |
| S1 | 105.0 | 32.2 | 3.11× | 7.0 |
| S0 | 124.2 | 38.1 | 2.63× | 2.1 |
| S2 | 136.9 | 42.0 | 2.38× | 11.4 |
| S3 | 326.2 | 100.0 | 1.00× | 27.2 |

### `medium/stlc` — 4 targets

Single runs.  The slowest is S3 at 911.2 s.  S2 was not run on this problem.

| method | time s | index | speedup | agent-min |
| --- | ---: | ---: | ---: | ---: |
| S1 | 373.3 | **41.0** | **2.44×** | 24.9 |
| S0 | 471.4 | 51.7 | 1.93× | 7.9 |
| S4 | 497.6 | 54.6 | 1.83× | 66.3 |
| S3 | 911.2 | 100.0 | 1.00× | 75.9 |

## Aggregate

The aggregate treats `gcd` and `stlc` equally.  **Mean index** is the
arithmetic mean of the per-problem indices.  **Geometric-mean speedup** is the
geometric mean of the per-problem speedups, which is the right average for
ratios.  **Compute vs S0** is the geometric mean of the per-problem
agent-minute ratios against S0.

| method | mean index | geometric-mean speedup | compute vs S0 |
| --- | ---: | ---: | ---: |
| S4 | 38.4 | **2.88×** | 6.3× |
| S1 | **36.6** | 2.75× | 3.3× |
| S2 | 42.0 (gcd only) | 2.38× | 5.5× |
| S0 | 44.9 | 2.25× | 1.0× |
| S3 | 100.0 | 1.00× | 11.3× |

## Mid-tier block

Two harder problems were added after the first block.  `dep-vec` was a
one-shot (54 s) and is not a method discriminator; `mergesort` and the bespoke
`ref-store` are.

### `medium/mergesort` — 6 targets

S0 is the slowest at 498.3 s.

| method | time s | index | speedup | agent-min |
| --- | ---: | ---: | ---: | ---: |
| S4 | 376.1 | **75.5** | 1.33× | 50.2 |
| S1 | 392.2 | 78.7 | 1.27× | 26.1 |
| S0 | 498.3 | 100.0 | 1.00× | 8.3 |

S4 is only **4%** faster than S1 for twice the agents.  The knee is at four
workers; the extra four buy attempts, not a shorter critical path.

### `medium/ref-store` — 4 targets

Bespoke STLC + references + heap typing.  S0 is the current slowest at 821.2 s.

| method | time s | index | speedup | agent-min |
| --- | ---: | ---: | ---: | ---: |
| S1 | 581.9 | **59.3** | **1.69×** | 38.8 |
| S2 | 620.4 | 63.2 | 1.58× | 53.3 |
| S4 | 801.4 | 81.7 | 1.22× | 106.9 |
| S0 | 821.2 | 83.7 | 1.20× | 13.7 |
| S3 | 981.3 | 100.0 | 1.00× | 84.3 |

S1 wins.  S2's broadcast nearly matches it but loses 6.6% of wall clock to the
supervisor/relay.  S4 is **worse than S2**, barely ahead of S0, and 7.8× S0's
compute; 63 checks produced no critical-path shortening.  S3 is slowest: its
plan alone took 5m42, even though every cut lemma integrated cleanly.

### Aggregate, mid-tier (`stlc` + `mergesort` + `ref-store`)

Equal weight per problem, ratio scale.

| method | mean index | geometric-mean speedup | mean agent-min |
| --- | ---: | ---: | ---: |
| S1 | **59.7** | **1.74×** | 29.9 |
| S4 | 70.6 | 1.44× | 75.2 |
| S0 | 78.5 | 1.00× | 10.0 |
| S2 | ref-store only | 1.58× | 53.3 |
| S3 | `stlc`+`ref-store` only | 1.00× | 84.3 |

S1 wins on wall clock and on compute.  S4 wins only the `mergesort` cell (by
4%) and loses the other two.  S2 is a close second on the one hard problem it
was run on, at higher compute.  S3 is slowest wherever it is measured.

## Reading

- **Easy tier:** S4 wins clearly (index 22.1, 4.52×) but uses 8 agents.  S1 is
  3.11× at 7.0 agent-minutes against S4's 9.6, so S1 buys most of the wall-clock
  gain at 73% of S4's cost on this problem.  S2's supervisor/relay overhead
  puts it essentially at S0.  S3's plan and integration cost more than the
  whole serial solve.
- **Medium tier:** S1 is best (41.0, 2.44×) and stable.  S4 is slower than S1
  (54.6, 1.83×) despite twice the agents and 54 checks; eight copies of the
  same long proof search do not shorten the critical path.  S3 is slowest
  (100) and 9.7× S0's compute.
- **Aggregate:** S4's 2.88× and S1's 2.75× are close, but S4 costs 6.3× S0's
  compute against S1's 3.3×.  Prefer S1 unless wall clock dominates and the
  problem is short.  S3 is not competitive in this block.
- **Index consistency:** S3 is slowest on both problems, which is what makes
  the 100 base the same method twice.  If S3 had not been run, each problem
  would renormalise and the indices would not be comparable across rows.

## PCF (hard tier)

PCF is **solved**: 12/12 by S7’s level-free LR lane in 19m24.  There is no
cross-method solve-time index because only S7 solved it.

| fact | value |
| --- | --- |
| current statement | **12 targets**: infrastructure, `contextual_le_value`, easy similarity, the pivot, congruence, assemblies |
| S1 cold | 4 agents, **7/12** at 24m14; first target 17.3m; 95 checks |
| S2 cold | 5 agents, **7/12** at 24m35; first target **9.2m**; 121 checks |
| S5 warm | 3 agents from 7/12, **8/12**; pivot green in **11m08** |
| S6 focused LR | LR core green; **8/12**; blocked on the step index |
| **S7 final** | **12/12 at 19m24**; 3 agents; 15 checks; 63.6 agent-min; 2002 lines |
| winning route | level-free `VL`/`EL`; `EL_app`, `EL_fundamental`, `EL_post_sim`; **no Howe** |

The cold runs stalled on duplicated de Bruijn infrastructure.  The warm start
removed that, the pivot fell in 11 minutes, and the final LR lane dropped the
step index and closed the remaining four targets.  The Howe lanes added no
targets; the winning route is a logical relation, not Howe.

The first PCF statement was wrong.  A one-directional relation called a
bisimulation let `omega` simulate `zero`; a second version related `zero` to
`succ zero` because the ground clause used the relation instead of value
equality.  A proposed sub-target `plug_steps` was also false (a context can put
the hole under a `lam`, and PCF does not step under binders).  All three were
found by agents and refuted in Lean; the superseded runs are `void`.  The
current statement uses one-directional `Simulates`, ground equality, and
`contextual_le_plug`; the pivot is split so partial work is scored.

The repaired retry is real progress: 7/12, including `contextual_le_value`,
which one agent proved without Howe.  The two remaining hard steps are the
ground-value discrimination in `contextual_le_implies_sim` and Howe's method.

## Raw solve times

| problem | S0 | S1 | S2 | S3 | S4 |
| --- | ---: | ---: | ---: | ---: | ---: |
| `gcd` | 138.9, 109.4 | 104.8, 105.2 | 136.9 | 326.2 | 72.2 |
| `stlc` | 471.4 | 373.3 | — | 911.2 | 497.6 |

`solve time` is first green check minus run start, in seconds.  It excludes
report-writing after the solve and includes the remote compile round trip
(about 8 s warm) and every failed attempt before the green one.

## Caveats

- One or two runs per cell.  The index is a description of this block, not a
  population estimate.  The S0/S1 `gcd` ranges almost touch (109.4–138.9 vs
  104.8–105.2), so their 1.18× mean gap is suggestive rather than decisive.
- S1's `stlc` interval overlapped S3/S4 on `gcd`; median check time stayed at
  about 8 s, but the cell should be repeated on a quiet worker.
- The honesty protocol is an honour system.  One S0 `gcd` repeat is excluded
  because its agent reported that a broad `find /` printed other runs' file
  paths (no contents read).  No run reported reading a proof.
- The PCF runs are partial; the hard-tier index is undefined until a method
  solves at least one problem completely.
- All numbers come from `runs/*/summary.json`, produced by
  `harness/score.py`; reproduction requires the same corpus hashes and method
  briefs.

## Bottom line

If the question is **wall clock on short problems**, S4.

If the question is **wall clock per unit of compute**, S1: 2.75× at 3.3× the
serial compute, against S4's 2.88× at 6.3×.

If the question is **the hard tier**, neither has an answer yet; PCF's 2/7 at
26 min says the bottleneck is a single deep lemma, not the number of agents.
