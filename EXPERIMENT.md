# Experiment: organisations for Lean proof work

## Claim under test

A group of agents can prove a fixed set of Lean theorems; the question is which
organisation converts a fixed wall-clock budget into the most verified proofs,
and at what cost in agent time.  The candidate organisations are a serial
worker, a blind race, a race with a progress-broadcasting supervisor, a
lemma-cutting supervisor, and a race with twice as many workers.

## Hypotheses

| id | hypothesis | what would refute it |
| --- | --- | --- |
| H1 | four blind workers solve a problem faster than one, but not four times faster | no wall-clock gain, or a gain only at disproportionate agent cost |
| H2 | broadcasting verified checkpoints beats blind racing | S2's problems/hour is not above S1's outside repeat noise |
| H3 | cutting a goal into lemmas and assigning them beats whole-proof search | S3 is slower, or its lemmas are green but unused at integration |
| H4 | doubling the blind swarm from four to eight is sublinear | S4/S1 rate ratio is near or below 1, or contention dominates |
| H5 | a DAG scheduler that runs ready nodes in parallel and chooses a method per node beats a flat method on a multi-node DAG at the same wall-clock budget | no wall-clock gain over the best flat method outside the repeat range, or a gain only at disproportionate agent-minutes or check contention |

## Design

The method is the only intended difference between runs.  Every run uses the
same statements, the same budget rule, the same brief shape, the same model and
the same toolchain.

* **Unit of work.** A problem is one statement module with one or more
  `def target : Prop`.  A target is accepted only when a proof declaration has
  exactly that type and its axioms are within the allowed set.  A comparison
  cell is one problem per run: the same statement is handed to every method
  separately, so a solve time is attributable to that problem and not to a
  queue of earlier ones.  The harness accepts several problems in one run for
  calibration, but those rows do not enter the method comparison.
* **Compile latency.** A check is a tar, an IAP copy and one remote shell; it
  measured 16.7 s cold and 7.6 s warm on the first worker.  That cost is in
  every method's clock, so agents are told to batch edits and check after a
  coherent attempt rather than after every tactic.
* **Budget.** Each problem has a per-problem budget in
  `problems/manifest.json`; a run's budget is the sum of its problems' budgets.
  A problem is unsolved at expiry.  The clock starts when the first agent is
  spawned and stops at `pa.py finish`.
* **Order.** Problems are worked in the order recorded in `run.json`, which is
  the order given to `new_run.py`.  The same order is used for every method.
* **Warm-up.** One smoke run per method is excluded from results; it checks
  that the brief, the harness and the agent spawning work.
* **Repeats.** The pilot has two clean repeats for S0 and S1 on `gcd` and one
  for each other cell.  The decision block uses three repeats per (method,
  problem set) for S0–S4; two for the hard set if cost binds.  Method order is
  rotated between repeats so a thermal or load drift is not attributed to a
  method.
* **Host.** One leased 8-vCPU / 16 GB Cloud worker from the
  `nixos-lean-x86-64` image.  Every check is compiled there; the local machine
  only edits and scores.  Up to eight elaborations of these small modules run
  concurrently under 16 GB.  The IAP tunnel and the sync are inside each
  check's wall clock, because a deployed workflow pays them too.  A worker that
  cannot be reached is a recorded backend error, not a local fallback.
* **Exclusions.** A run with a confirmed cheating report, a harness failure, or
  an agent that never started is excluded and repeated.  The exclusion and its
  reason are recorded in `run.json`.

## Methods

| id | workers | supervisor | communication | stop |
| --- | ---: | ---: | --- | --- |
| S0 | 1 | — | none | first green |
| S1 | 4 | — | none | first green |
| S2 | 4 | 1 | verified checkpoints on a board, broadcast to workers | first green |
| S3 | 4 | 1 | lemma plan, assignments, verified lemmas copied into a shared root | first green root |
| S4 | 8 | — | none | first green |
| S5 | 3 | — | none; warm start from a verified partial proof, three different strategies | first 12/12 |

The briefs are in `methods/`.  S5 is a continuation experiment, not a cold
method: all three lanes start from the same 7/12 PCF proof and differ only in
strategy (value/pivot, Howe, non-Howe congruence).  The conductor (the session that spawns the
agents) carries messages between supervisor and workers for S2 and S3; that
relay time is inside the measured wall clock, because a deployed cross-talk
supervisor would also spend it.

## DAG scheduling (H5)

H5 is a scheduler, not a run-level method.  It replaces "one method for one
problem" with "one method for one ready node".

A node is:

```text
id, statement, dependencies, owner file, check command, budget,
truth status (known/expected/open), lane count
```

The scheduler:

1. runs a specification-falsification phase first, with several independent
   counterexample attempts per new node; the first machine-checked refutation
   stops that node and starts serial core repair;
2. freezes a verified warm base and starts only nodes whose dependencies are
   green;
3. chooses a method per node: S0 for small or tightly coupled nodes, S1/S3 for
   independent lemma sets, S5 for the critical hard lemma, S2 only when
   verified definitions are genuinely reusable;
4. prioritises the critical path, not raw occupancy;
5. allows one writer per file; the scheduler copies verified modules into the
   shared root and never lets two workers edit the same file;
6. stops sibling lanes at first green and merges immediately.

The test compares the DAG scheduler with the best flat method on the same
multi-node DAG, same warm base, host, budget, and check policy.  Primary
endpoint: wall-clock to every node green.  Secondary: agent-minutes, checks,
critical-path stalls, and contention.  A flat one-problem-per-run harness cannot
test H5; the scheduler must be implemented before the cell is run.


## Corpus

| tier | problem | targets | why it is here |
| --- | --- | --- | --- |
| smoke | arithmetic | 2 | validates harness, hashes, axiom check |
| easy | gcd | 2 | bounded Euclid; arithmetic and divisibility |
| easy | sort | 2 | insertion sort; sortedness and permutation |
| easy | stack | 1 | compiler correctness for arithmetic expressions |
| medium | stlc | 4 | extrinsic STLC: substitution, progress, preservation, determinism |
| medium | regex | 1–2 | Hutton–Rosen matcher against an inductive language |
| medium | avl | 3 | rotations preserve BST and balance |
| medium | framed-refines | 5 | framed refinement algebra, modelled on `lean-llvm` |
| medium | dep-vec | 2 | dependent vectors: preservation and progress, from `rocq-piler`'s `dep_vec` challenge |
| medium | mergesort | 6 | merge/split correctness, sortedness and permutation, from `rocq-piler`'s `mergesort` challenge |
| hard | lambda-cr | 4 | Church–Rosser by parallel reduction |
| hard | stlc-norm | 4 | strong normalisation by Tait candidates |
| hard | imp-compiler | 2 | compiler correctness for a small imperative language |
| hard | pcf | 7 | contextual may-preorder ↔ applicative similarity; equivalence both ways |

The PCF problem is deliberately a ladder: reflexivity and the application
clause are easy, `contextual_le_implies_sim` is the standard easy direction,
`sim_congruent` is Howe's method, and the preorder and the equivalence are
assembled from those.  `Simulates` is one-directional: `omega` simulates
`zero` but not conversely, so `contextual_eq_iff_sim_both` is not derivable
from one direction.

The first PCF statement called the union of one-directional relations a
bisimulation and concluded equivalence from one direction.  Its agent proved
the equivalence targets **false** and the statement was corrected; that run is
marked `void` and is excluded from the method table.  The correction is
recorded in `results/README.md` and `docs/pcf.md`.

### Why these problems

* They span the failure modes a proof agent meets: a definition to unfold, a
  generalisation that must be found, an induction that must be strengthened, a
  library lemma that must be located, and a multi-file integration.
* The easy tier calibrates the harness and gives a non-zero rate even when the
  hard tier is unsolved; the hard tier separates methods that only differ under
  sustained search.
* None needs mathlib, so a check is sub-second and an eight-way race does not
  spend its budget elaborating dependencies.
* The answers are standard results, so a target that no method ever proves is
  evidence about the method, not about the statement — provided the statement
  compiles and is the standard one.  Statements are reviewed before a run.

## Measurement

`harness/pa.py check` appends one JSON line per check to `runs/<id>/events.jsonl`:
agent, problem, start/end timestamps, build time, per-target type-check and
axiom result, forbidden-construct findings, statement hash result.  A solve is a
check whose every target is green.  `harness/score.py` turns the events plus
`run.json` into `summary.json` and `summary.md`.

Primary endpoint: **problems solved per wall-clock hour at the budget**.
Secondary: targets per hour, time-to-solve distribution, agent-minutes per
solve, checks per solve, failed-check ratio, and for S2/S3 the reuse and
lemma-integration counts.

A run that solves `k` of `n` has a censored observation for the rest; report
the solve fraction and the time-to-solve of the solved ones separately.  Do not
report a mean solve time over solved problems alone as if it were the method's
time.

## Pilot

`results/README.md` holds the first block: all five organisations on
`easy/gcd`, and S0/S1 on `medium/stlc`.  It is one run per cell — enough to
size the overheads and catch a broken protocol, not enough to choose a method.
The large effects (S3's plan cost, S2's relay cost, S1's wall-clock gain at
3× agent cost) are visible; the small differences are not.

## Retrospective

The retrospective is written after the repeats and reads only `summary.json`,
`events.jsonl` and the run notes.

1. **Rate by method and tier.**  Problems/hour and targets/hour, with the
   repeat range.  A difference smaller than the repeat range is not a result.
2. **Cost.**  Agent-minutes/solve and checks/solve.  A method that wins the
   clock at several times the agent cost is labelled as such.
3. **Shape of the work.**  Time-to-solve distribution and the fraction of
   budget used before the first green check.  A method that produces a late
   burst is different from one that is steady even at the same total.
4. **Coordination.**  For S2: checkpoints broadcast, imported, and ignored.
   For S3: lemmas cut, re-cut, green but unused, and supervisor minutes after
   the last worker checkpoint.
5. **Failures.**  Read the notes and classify: did not understand the
   statement, could not find the generalisation, tactic loop, library lemma
   missing, integration conflict, or ran out of budget.
6. **Decision.**  Choose the method with the best rate among those whose cost
   is acceptable; if the rates are within the repeat range, choose the simpler
   organisation.  Record the choice and the evidence in `results/`.

### What would change the decision

* A method whose advantage appears only on the hard tier suggests the easy tier
  is too small to measure organisation.
* A method that wins on rate but loses on targets/hour is buying finished
  problems by abandoning partial progress; that is a real trade, not noise.
* S4's ratio below ~1.4 means the marginal worker is not buying its cost on
  this host, whatever the hard tier does.

## Threats to validity

* **Honour system.**  `../lean-llvm` and the open web are reachable.  The
  harness detects a changed statement, a `sorry`, an `axiom` and
  `native_decide`; it cannot detect a read proof.  Every agent reports
  exposures; a confirmed exposure invalidates the run.  Treat a rate as an
  upper bound if the exposure log is not clean.
* **Small n.**  Three repeats per cell is enough to see a large effect, not a
  small one.  Report ranges, not p-values.
* **Problem selection.**  The corpus is chosen by the experimenter and may
  favour the kind of proof an agent is good at.  The per-tier split makes that
  visible; it does not remove it.
* **Model and prompt drift.**  The model is whatever the session provides; the
  brief is versioned by hash in `run.json`.  Compare only runs with the same
  hashes.
* **Host contention.**  Eight agents on eight cores contend for elaboration and
  memory; that is part of the deployed rate, but it makes S4's result a
  statement about this host, not about eight agents in general.
* **Statement correctness.**  A false target is unsolvable and would look like
  a method failure.  Every statement is compiled before a run; the standard
  theorems are reviewed against their definitions.  There is no independent
  proof of every target before the experiment, because that would be the
  answer.
* **Learning.**  Agents do not share memory across runs, but the experimenter
  does; the brief and the corpus must not be tuned between methods mid-block.

## On `lean-llvm`

`Problems/Medium/FramedRefines.lean` states the algebra of a framed refinement
relation at the shape `lean-llvm` uses; it is self-contained, not a port.
A literal port of a `lean-llvm` theorem would need its import cone vendored and
would put the original proof in a sibling checkout, which the honour system
then has to exclude.  Decide that trade before adding one.

## Other candidate problems

Not in the first corpus, in rough order of expected cost:

* Hindley–Milner: soundness and completeness of algorithm W, or principal
  types for a let-free fragment.
* Defunctionalisation or CPS conversion: semantics preservation.
* Separation-logic soundness for a small while language (the frame rule is the
  interesting part).
* Normalisation by evaluation for STLC, with the reification/reflection
  lemmas.
* Binary GCD and its bit-level invariant.
* Okasaki-style amortised queues with a potential function.
* König's lemma / infinite pigeonhole, if a mathlib-free encoding is wanted.
* PCF variants: environmental bisimulation, or a step-indexed logical relation
  instead of applicative bisimulation.
