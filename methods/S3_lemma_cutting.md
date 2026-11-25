# S3 — lemma-cutting supervisor

**Question:** does decomposing the goal into independent lemmas and assigning
them beat letting each worker search the whole proof?

## Organisation

Four workers, `a1`–`a4`, and one supervisor, `s1`.  The supervisor owns
`shared/workspace` and the lemma plan.

### Cut protocol

Before workers start a problem, the supervisor writes
`runs/<id>/shared/plan.md`:

```
## plan <problem id> <UTC time>
root: <the target declarations>
lemmas:
  L1: <exact Lean statement>   owner: a1   depends: —
  L2: <exact Lean statement>   owner: a2   depends: L1
  ...
integration: <who owns the file that assembles the root from the lemmas>
```

A cut is admissible only when every lemma statement is a Lean proposition the
supervisor has elaborated (it lives in a file that builds), and the root's
proof would follow from the lemmas.  Guessing at statements is not a cut.

The supervisor assigns each lemma to one worker.  A worker proves only its
lemmas, in its own workspace, and reports a checkpoint when a lemma builds.
The supervisor copies the green lemma into `shared/workspace/Proofs/` under a
unique name, adjusts the plan, and tells dependents that their dependency is
available.

### Re-cutting

A lemma that has not moved in one third of the remaining budget is split again
or reassigned.  A cut that no worker can start because a dependency is missing
is a supervisor error; the supervisor fixes the plan rather than asking a
worker to guess.

### Integration

The supervisor owns the root module in `shared/workspace`.  It may not change
a worker's file; it copies the declaration it verified.  The root is green
only when every lemma it names is green and the assembled module checks.

## Clock and stopping

The clock starts when the supervisor is spawned.  The problem ends at the
first green root check in the shared workspace.  The run ends when every
problem is green or the budget expires.

## What is measured

- problems per wall-clock hour;
- agent-minutes per solve (five agents charged);
- **parallel efficiency**: sum of worker-minutes spent on lemmas divided by
  the critical-path wall clock;
- cut quality: lemmas re-cut, lemmas never started, lemmas green but unused;
- integration cost: supervisor minutes after the last worker checkpoint;
- checks and failed checks per solve.
