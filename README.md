# proof-approach

An experiment, not a library: **how fast can a group of Lean agents move
through a fixed set of proofs, and which organisation moves fastest?**

The subject is the organisation, not any one proof.  A corpus of statements is
copied into isolated run environments; agents in different organisations try to
prove them under the same wall-clock budget; the harness records every compile,
every accepted target and the time each one landed.  The numbers feed a
retrospective that chooses the next organisation rather than guessing.

No reference proof is stored in this repository.  A target is accepted only
when a declaration has exactly the declared type and its axiom footprint is a
subset of `propext`, `Classical.choice`, `Quot.sound` — no `sorry`, no
`native_decide`, no new `axiom`.  The statement files are hashed, so weakening
a statement fails the run.

## Compilation runs on a Cloud worker

Elaborating eight Lean proofs on one desktop exhausts it.  Checks are compiled
on a leased Cloud worker; the local machine only edits files and reads the
output.  A check syncs the workspace to the worker, runs `lake build` and the
target checks there, and appends the event locally.

The worker is one 8-vCPU / 16 GB spot machine from the `nixos-lean-x86-64`
image (Lean 4.35.0 and Lake on its PATH), leased for the run and deleted at the
end.  Eight concurrent elaborations of these small modules fit under 16 GB;
each check is one tar and one remote shell.

Write `.remote.json` after creating the worker:

```json
{
  "backend": "remote",
  "session": "<omp-session-id>",
  "worker": "lean-prover-<session-prefix>",
  "zone": "europe-west9-a",
  "remote_root": "$HOME/pa",
  "lake": "lake"
}
```

Without the file, `pa.py` compiles locally; that path exists for the harness
self-test (`--local`) and is not used for a measured run.  A worker that cannot
be reached is a failed check, never a silent local build.

### Recreating the worker

From the omp-tools pack checkout:

```bash
bun scripts/gcloud-worker.ts create --purpose lean-prover --cores 8 \
  --memory-gb 16 --disk-gb 50 --lease 4h --session <omp-session-id> --lean
```

The image's `lake` on `PATH` is the lean-llvm wrapper, which copies an 8 GB
mathlib package cache on first use; use the unwrapped store path instead:

```bash
bun scripts/gcloud-remote.ts run --session <omp-session-id> -- \
  "head -5 /run/current-system/sw/bin/lake"
```

Put that `/nix/store/...-lean4-4.35.0/bin/lake` in `.remote.json` as `lake`.
Delete the worker at the end of the block with
`bun scripts/gcloud-worker.ts delete --session <omp-session-id>`.

## Quick start

The toolchain comes from the flake; nothing needs to be activated.

```bash
# Inspect the corpus; this does not compile a proof.
nix develop -c python3 harness/pa.py list
# `nix develop -c lake build` elaborates the statements only, for inspection;
# measured checks compile on the worker through pa.py.

# A smoke run, end to end.
python3 harness/new_run.py --method S0 --tier smoke --budget-s 300
python3 harness/pa.py start --run <run-id>
python3 harness/pa.py check --run <run-id> --agent a1 --problem smoke/arithmetic
python3 harness/pa.py finish --run <run-id>
python3 harness/score.py --run <run-id>
```

A measured run is created the same way with a method and a problem set; the
brief written into each workspace is the agent's instruction sheet:

```bash
python3 harness/new_run.py --method S1 --tier easy --budget-s 3600
```

## Layout

```
Problems/                 statements: definitions and `def target : Prop`, no proofs
Proofs/                   the repository's own smoke proof; runs get skeletons
Problems.lean             library root for the statements
problems/manifest.json    ids, tiers, targets, required proof names, budgets
methods/                  one brief per organisation (S0–S4)
harness/pa.py             compile, type-check, axiom-check, append an event
harness/new_run.py        copy statements into workspaces, hash them, write briefs
harness/score.py          events → summary.json / summary.md / method comparison
runs/                     one directory per run (generated, not committed)
results/                  comparison tables produced by score.py
```

## Measures

| measure | definition |
| --- | --- |
| problems/hour | solved problems ÷ wall-clock hours for the run |
| targets/hour | accepted targets ÷ wall-clock hours (partial credit) |
| agent-minutes/solve | allocated agent wall-clock ÷ solved problems |
| time to solve | first green check − run start |
| checks/solve | total compile+check invocations ÷ solved problems |
| reuse rate | checkpoints broadcast and imported by another worker (S2/S3) |

Wall clock is the headline because that is what a person waiting on the work
experiences.  Agent-minutes are reported beside it because a method that wins
the clock by using five times the compute is not obviously the one to deploy.

## Pilot result

One run per cell, first green check, remote worker.  Full tables and caveats
are in [results/README.md](results/README.md).

| problem | S0 (1) | S1 (4) | S2 (5) | S3 (5) | S4 (8) |
| --- | ---: | ---: | ---: | ---: | ---: |
| `easy/gcd` solve s | 138.9 | 104.8 | 136.9 | 326.2 | 72.2 |
| `easy/gcd` rate/h | 25.9 | 34.4 | 26.3 | 11.0 | 49.9 |
| `easy/gcd` agent-min | 2.3 | 7.0 | 11.4 | 27.2 | 9.6 |
| `medium/stlc` solve s | 471.4 | 373.3 | — | 911.2 | 497.6 |
| `medium/stlc` rate/h | 7.6 | 9.6 | — | 4.0 | 7.2 |

The large effects are S3's planning/integration overhead and S4's rate.  Across
two clean repeats S1's mean on `gcd` is 105 s against S0's 124 s (1.18×) at 4×
the agent-minutes; the ranges almost touch, so that gap is suggestive, not
decisive.  The S0/S1/S2 differences need the repeat block.

## Honesty

The environments are not sealed.  A run is valid only if its agents follow the
brief: no reading `../lean-llvm`, no other workspace, no web search for the
theorem, no reference proof.  Every agent is asked to report an exposure with
`pa.py note --cheat`; a confirmed exposure invalidates the run and it is
repeated.  The harness catches the mechanical escapes (statement edits,
`axiom`, `sorry`, `native_decide`) and cannot catch reading a proof.  The
experiment's conclusions are only as good as that honour system.

See [EXPERIMENT.md](EXPERIMENT.md) for the design, the method definitions, the
retrospective plan and the threats to validity.
