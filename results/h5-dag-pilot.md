# H5 pilot: DAG scheduling vs flat methods

## Hypothesis

H5: a DAG scheduler that runs ready nodes in parallel and chooses a method per
node beats a flat method on a multi-node DAG at the same wall-clock budget,
without a disproportionate agent-minute or check-contention cost.

## Setup

- Held-out nodes: `easy/gcd` and `easy/stack`.
- No reference proof was present in `Proofs/` for either node during the pilot.
- Local checks through `harness/pa.py check --local`.
- One run per arm; no repeat. Start times within 60 ms for the balanced arm.
- The DAG arms were launched manually: one run per node. This is a scheduler
  prototype, not the final scheduler implementation.

## Result

| arm | total workers | node allocation | wall-clock | agent-min |
| --- | ---: | --- | ---: | ---: |
| S0 serial | 1 | gcd then stack | 3m19 | 3.3 |
| S1 flat | 4 | blind race over both | 1m39 | 6.6 |
| DAG, 1/node | 2 | 1 gcd, 1 stack | 2m58 | 3.6 |
| **DAG, balanced** | **4** | **3 gcd, 1 stack** | **1m20** | **4.5** |

Balanced DAG node completions:

- `easy/stack`: 30.3 s.
- `easy/gcd`: first green at 1m20 (lanes at 1m20, 1m23, 1m29).

The balanced DAG was **19 s faster than S1 flat** (1m20 vs 1m39) with the same
total worker count, and used **4.5 agent-min vs 6.6**. S0 serial used fewer
agent-min (3.3) but was much slower.

The underpowered 2-worker DAG lost to S1: one worker per node is bounded by the
slowest node. H5 is not "put one worker on every node"; it is "allocate lanes
to the critical node."

## Interpretation

This pilot supports H5 for a two-node DAG with a clear critical node. It does
not establish a general ranking:

- one sample, one repeat;
- small problems and short solve times;
- manual per-node launch rather than a scheduler;
- launch and check overhead are not isolated;
- S1's first-green time is 1m39, but two S1 workers reached it independently.
- The S1 agent-minute figure is the **stop-rule cost** (4 workers for 1m39).
  The manual controller did not kill the remaining lanes; one completed at
  4m20 and another S1 lane also continued. Those late completions are excluded
  from the method endpoint but are a reminder that a real scheduler must
  enforce the kill.

The next H5 test needs a real scheduler, a wider held-out DAG, repeats, and a
measurement of scheduler overhead separate from solve time.

## Harder cell

Two independent held-out medium nodes:

- `medium/stlc` — 4 targets
- `medium/mergesort` — 6 targets

| arm | workers | allocation | both nodes green | agent-min |
| --- | ---: | --- | ---: | ---: |
| S1 flat | 4 | blind race both | 9m10 | 36.7 |
| **DAG balanced** | **4** | **3 mergesort, 1 stlc** | **5m40** | **20.3** |

Node times:

| node | DAG first green | S1 first green |
| --- | ---: | ---: |
| mergesort | 4m53 | 5m24 |
| stlc | 5m40 | 9m10 |

The balanced DAG was 3m30 faster and used roughly half the agent-minutes. The
critical node was STLC for the DAG, not mergesort: allocating three lanes to
mergesort was based on target count, not measured difficulty. A scheduler with
cost estimates would move a lane to STLC.

Caveats: one run, manual per-node launch, no repeats, and the S1 remaining lanes
were stopped after both nodes were green. This is consistent with H5, not a
general ranking.


## Artifacts

Proofs from these arms remain in the ignored `runs/h5-*` directories, not in
`Proofs/`, so the corpus stays held-out.

## Scheduler backend smoke

`harness/dag.py --spawn` on a one-node `easy/gcd` DAG:

```text
created h5-real-gcd
start gcd (S0, 1 lane) 14:12:48.778Z
solved gcd             14:14:14.856Z  (86.1s)
stopped siblings
DAG result: solved
```

This validates the `omp -p` worker adapter, first-green event detection, and
sibling shutdown.  It is not an H5 comparison: one node, one arm, and the
`easy/gcd` proof is already known from the corpus runs.

