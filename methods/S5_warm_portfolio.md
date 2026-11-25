# S5 — warm-started strategy portfolio

**Question:** once the shared infrastructure and the easy targets are already
proved, does a small portfolio of *different* strategies finish a very hard
problem faster than another cold blind race?

This is a continuation experiment, not comparable to cold S0–S4 runs.  Every
worker starts from the same verified **7/12** PCF proof; the remaining work is
the value/pivot target and Howe.

## Organisation

Three workers, `a1`–`a3`, each with its own workspace and the same warm-start
proof copied into `Proofs/`.  No communication.

Each lane has a different brief:

| lane | strategy |
| --- | --- |
| `a1` | value/ground first: `contextual_le_implies_sim` via value separation and a divergent term; then assemblies |
| `a2` | Howe first: `sim_congruent` via a Howe relation; then assemblies |
| `a3` | non-Howe congruence: prove `sim_implies_contextual_le` directly by CIU / context lemma / logical relation; then assemblies |

The first workspace whose `pa.py check` reports **all 12 targets green** wins.
The conductor stops the other two immediately.  Partial targets are scored:
8/12, 9/12, 10/12, 11/12 are all meaningful results.

## Why warm start

The cold runs showed that every worker rebuilds the same 400–650-line
substitution/renaming/context library before touching the hard step.  The warm
start removes that duplication and isolates the research question: can a
strategy lane finish the remaining five targets?

## Measurement

- targets gained after the warm start, and time to each new target;
- time to 12/12, if reached;
- proof lines and declarations added;
- agent-minutes from the warm start;
- which strategy reached which target.

## Rules

- The statement is immutable; the warm-start proof is the starting `Proofs/`
  tree.
- Every check goes through `pa.py` on the remote worker.
- No reference proof, no other workspace, no web search, no subagents.
