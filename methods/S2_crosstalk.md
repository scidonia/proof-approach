# S2 — swarm with a cross-talk supervisor

**Question:** does broadcasting progress between four workers beat four blind
attempts?

## Organisation

Four workers, `a1`–`a4`, and one supervisor, `s1`.  Each worker has its own
workspace; the supervisor owns `shared/workspace` and the board.

### Board protocol

A worker that reaches a **kernel-checked checkpoint** appends to
`runs/<id>/shared/board.md`:

```
## <agent> <UTC time>
status: checkpoint | blocked | abandoned | solved
problem: <id>
file: <workspace-relative path>
declarations: <fully-qualified names, one per line>
builds: nix develop ... pa.py check --run ... --agent <agent> --problem <id>
note: <one paragraph: what is proved, what failed, what the next step is>
```

A checkpoint is only a declaration that the named module builds and the named
targets are green.  Scratch reasoning, "I think this works", and an unbuilt
file are not checkpoints.

The supervisor reads the board, verifies a claimed checkpoint by running the
worker's check itself (or by reading the event it produced), and writes
`runs/<id>/shared/broadcast.md`:

```
## broadcast <UTC time>
usable: <declaration name> — <workspace path> — <what it gives you>
avoid: <approach that failed and why>
next: <one suggestion per worker, or "keep going">
```

The supervisor broadcasts only what it has verified.  A declaration whose
build is red is not broadcast; it is reported as failed.

### Worker rules

- Work on the same problem as the swarm, not on a private replacement.
- Read `broadcast.md` before starting a new attempt and after every checkpoint.
- You may copy a broadcast declaration into your own workspace **with its
  file path and a comment naming the source agent**.  You may not edit another
  workspace.
- Do not wait for the supervisor.  The broadcast is an accelerator, not a
  gate.

The conductor carries the messages: a worker ends its turn at a checkpoint,
the conductor wakes the supervisor with the board delta, then wakes each
worker with the new broadcast.  The relay latency is part of the method's
wall clock and is recorded in the events.

## Clock and stopping

The clock starts when the workers are spawned.  The problem ends at the first
green check in any worker workspace.  The run ends when every problem is green
or the budget expires.

## What is measured

- problems per wall-clock hour;
- agent-minutes per solve (five agents charged);
- **reuse rate**: checkpoints broadcast and checkpoints imported by a worker
  other than their author;
- checks and failed checks per solve;
- relay turns (supervisor messages) per solve.

If cross-talk does not improve the rate, the extra agent and the relay are
cost without a return; that is the result, not a failure of the run.
