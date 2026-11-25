# Best approach on mid-to-hard: S1 (four blind workers)

Complete for the completed cells.  `ref-store` now has all five methods.

| problem | S0 | S1 (4) | S2 (5) | S3 (5) | S4 (8) |
| --- | ---: | ---: | ---: | ---: | ---: |
| `stlc` | 471.4 | **373.3** | — | 911.2 | 497.6 |
| `mergesort` | 498.3 | 392.2 | — | — | **376.1** |
| `ref-store` | 821.2 | **581.9** | 620.4 | 981.3 | 801.4 |

## Aggregate, three mid-tier problems

Equal weight per problem, ratio scale.

| method | mean index | geometric-mean speedup | mean agent-min |
| --- | ---: | ---: | ---: |
| S1 | **59.7** | **1.74×** | 29.9 |
| S4 | 70.6 | 1.44× | 75.2 |
| S0 | 78.5 | 1.00× | 10.0 |
| S2 | `ref-store` only | 1.58× | 53.3 |
| S3 | `stlc` + `ref-store` only | 1.00× | 84.3 |

S1 wins on wall clock and on compute.  It beats S0 by 1.26× on `stlc`, 1.27×
on `mergesort`, and 1.41× on `ref-store`.  S4 wins only `mergesort`, by 4%,
and loses the other two; on `ref-store` it is 1.02× S0 at 7.8× the compute.
S2 is a close second on `ref-store` (1.58×) but pays for the broadcast/relay.
S3 is slowest wherever it is measured: its `ref-store` plan alone took 5m42,
even though every lemma integrated cleanly.

## Why

Four independent attempts are the knee.  Extra agents generate more attempts,
not a shorter critical path: S4 produced 63 checks against S1's 9 on
`ref-store`, 54 against 8 on `stlc`.  S2's communication is real but small:
one broadcast, one relay, and the workers still do the same four proofs; it
recovers part of S1's gain, not a different gain.  S3's cut is sound but
serialises the work behind a plan and an integration step.

## Decision

- **Mid-to-hard: S1 by default.**  Four blind workers, no communication, first
  verified green wins.
- **Short searches: S4** when one attempt can land (`gcd`: 72 s vs 105 s).
- **Agent-minutes first: S0.**
- **S2** only when a shared checkpoint is expected to prevent a known repeated
  dead end; it did not here.
- **S3** only when the plan can be amortised over a much larger proof than
  these.
