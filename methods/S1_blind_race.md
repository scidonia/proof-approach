# S1 — blind racing swarm of four

**Question:** does four independent attempts finish a proof faster than one,
and at what cost in agent-minutes?

## Doctrine

1. **One problem, four full attempts.**  No decomposition, no assigned
   lemmas, no specialisation.  Each worker may choose its own strategy and
   write its own helper lemmas.
2. **Isolation is the method.**  Separate workspace, identical statements and
   skeleton; no peer reading, no board, no shared artifacts.
3. **A green harness check is the only signal.**  An agent's claim, a partial
   proof, or a file that "should work" is not a win.  The check must accept
   every target with an allowed axiom footprint.
4. **First green wins; the rest are stopped immediately.**  No merge, no
   consensus, no second round.  The winning workspace is the deliverable.
5. **No supervisor and no relay.**  The conductor starts the clock, spawns the
   four, watches for the first green, kills the losers, and scores.  Nothing
   is broadcast.
6. **Stop on green.**  No polishing, no refactoring, no proof golf.
7. **Cost is explicit.**  Four agents for the whole solve interval; report
   wall clock and agent-minutes together.
8. **One problem per run** for attributable timing; the same statement and
   budget are used for every method.
9. **Honesty is part of the method.**  No reference proof, no other
   workspace, no web search; report an exposure and void the run.
10. **No subagents, no local compile.**  One worker per workspace; every check
    goes through `pa.py` to the remote worker.

The doctrine is a bet on the lower tail of the proof-search distribution: four
independent samples, no coordination cost.  It pays when one attempt can land
in a short time; it saturates when the proof is one long critical path, which
is why S4 adds little on `stlc` and `ref-store`.

## Organisation

Four workers, `a1`–`a4`, each with its own workspace and an identical copy of
the statements and the empty proof skeleton.  For a given problem they all
start together and work independently.

- No agent may read another agent's workspace, the shared workspace, or the
  board.  The workspaces exist to make that the default, not to enforce it;
  the honesty rule in the brief applies.
- The first workspace whose `pa.py check` reports every target green wins.
  The conductor stops the other three immediately.
- The winning proof is kept.  The other workspaces are recorded but not
  scored; their failed attempts are evidence about variance, not about the
  winner.

Problems are raced in the order recorded in `run.json`.  A race that hits the
per-problem budget is recorded as unsolved and the next problem starts.

## Clock

The run clock starts when the four workers are spawned.  A problem's solve
time is the first green check for that problem minus the race start.  The run
ends when the last problem is green or the total budget expires.

## What is measured

- problems solved per wall-clock hour (the headline);
- agent-minutes per solve (four agents' wall clock is charged);
- variance: how many of the four reached green, and the spread of their
  times, if more than one did before being stopped;
- checks and failed checks per solve.

This isolates the value of independent search from the value of
communication.  S4 repeats it at eight workers.
