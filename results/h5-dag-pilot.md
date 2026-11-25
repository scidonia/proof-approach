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

The next H5 test needs a real scheduler, a wider held-out DAG, repeats, and a
measurement of scheduler overhead separate from solve time.

## Artifacts

Proofs from these arms remain in the ignored `runs/h5-*` directories, not in
`Proofs/`, so the corpus stays held-out.
