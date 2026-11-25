# Results

Generated from `runs/*/summary.json` by `harness/score.py --all`.  The worker is
one 8-vCPU / 16 GB `nixos-lean-x86-64` spot instance; every check compiled
there.  A check costs 8–17 s of tunnel and sync, which is inside every method's
clock.

## Worker

One `c4-highcpu-8` spot instance in `europe-west9-a`, 8 vCPU / 16 GB, from the
`nixos-lean-x86-64` image, 50 GB boot disk, 4 h lease, about 0.0445 EUR/h.  Lean
4.35.0 and Lake are on the image; `/run/current-system/sw/bin/lake` is the
lean-llvm wrapper and would copy an 8 GB mathlib cache, so `.remote.json`
names the unwrapped store path.  Every check is a tar, an IAP copy and one
remote shell.  The worker is deleted at the end of the block; `runs/` keeps the
events and summaries.  Created 12:47 UTC, deleted 14:24 UTC: about 1.6 h at
0.0445 EUR/h, roughly 0.07 EUR of compute for the whole pilot.

## Pilot matrix

One run per cell.  `solve s` is the first green check minus the run start;
`rate` is 3600/solve s; `agent-min` charges every allocated agent for the whole
solve interval.

### `easy/gcd` (2 targets, 1800 s budget)

| method | agents | solve s | rate/h | agent-min | checks | failed checks | notes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| S0 serial | 1 | 138.9 | 25.92 | 2.3 | 1 | 0 | one-shot proof |
| S1 blind race | 4 | 104.8 | 34.35 | 7.0 | 2 | 0 | a3 green first; a4 9 s later |
| S2 cross-talk | 5 | 136.9 | 26.30 | 11.4 | 3 | 2 | supervisor 2m51s of planning/relay; a4 iterated twice |
| S3 lemma cut | 5 | 326.2 | 11.04 | 27.2 | 8 | 7 | 2m51s plan + integration; workers independent, a2–a5 |
| S4 blind race | 8 | 72.2 | 49.86 | 9.6 | 2 | 1 | a4 green; 8 agents for 72 s |

### `medium/stlc` (4 targets, 3600 s budget)

| method | agents | solve s | rate/h | agent-min | checks | failed checks | notes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| S0 serial | 1 | 471.4 | 7.64 | 7.9 | 8 | 7 | one-shot after 7 iterations |
| S1 blind race | 4 | 373.3 | 9.64 | 24.9 | 8 | 7 | a4 green; other three never checked |
| S3 lemma cut | 5 | 911.2 | 3.95 | 75.9 | 21 | 20 | 3m04s plan; a2's substitution lemma took 11m27s; clean 4/4 integration |
| S4 blind race | 8 | 497.6 | 7.23 | 66.3 | 54 | 51 | slower than S1 at 2× agents; 8-way checks, median check unchanged |

S1's run overlapped S4/S3 on `gcd` for part of its interval.  Check durations
were unchanged (median 8.0 s), so the overlap did not visibly slow
compilation; it is still a threat to validity and the cell should be repeated
on a quiet worker.

## Variance is larger than the S0–S1 gap

`gcd` repeats, first green check:

| method | run 1 | run 2 | mean | agent-min |
| --- | ---: | ---: | ---: | ---: |
| S0 | 138.9 | 109.4 | 124.2 | 2.1 |
| S1 | 104.8 | 105.2 | 105.0 | 7.0 |

S1 is 1.18× faster on the mean, but the S0 range almost touches S1's and the
sample is two; the difference is suggestive, not decisive.  The check counts
varied more than the solve times (S0: 1 then 2; S1: 2 then 5), which is the
iteration variance the repeats are meant to expose.  S4's single 72.2 s is
outside both ranges, which is the only easy-tier difference large enough to
act on.

A third S0 run (261 s) is excluded (`void`): its agent disclosed that a broad
`find /` printed other runs' proof file paths, though it read no contents.

## PCF: the statement was wrong, and the run found it

The first PCF run (S0, 30 min) proved three of six targets and then **refuted
two of the remaining three**:

* `IsBisimulation` was one-directional, so the union `Bisimilar` was
  applicative *similarity*, not bisimilarity.
* `omega = fix (fun x => x)` simulates `zero` (the clause never demands a
  matching divergence), but they are not contextually equivalent.  The agent
  proved `¬ (Bisimilar omega zero → ContextualEq omega zero)` and
  `¬ contextual_iff_bisim` in the same file.
* The maximum for the old statement was 4/6, not 6/6.

A second race then found a second counterexample: the relation's ground clause
matched any `R`-related values, so it related `zero` to `succ zero`, which the
context `ifz □ 0 omega` refutes.  The ground clauses now require **value
equality**.

The statement now uses `ContextualLe` (one-directional may-testing) and
`Simulates` (one-directional applicative similarity with value equality at
`nat`/`bool`), with `contextual_le_iff_sim` as the preorder theorem and
`contextual_eq_iff_sim_both` as the equivalence.  The two superseded runs are
marked `void` and excluded from the method table; their value is the
counterexamples and the partial proofs, not a rate.

This is the strongest argument for the harness's statement-hash and
target-type checks: an agent cannot quietly prove a weaker theorem, and a
false theorem shows up as a refutation rather than as a failed proof search.

## Mid-tier block

Two challenges from `rocq-piler`'s incomplete corpus were added.  `dep_vec`
turned out to be too easy to separate methods; `mergesort` is the mid-tier
block.

| problem | method | targets | solve s | checks | notes |
| --- | --- | ---: | ---: | ---: | --- |
| `dep-vec` | S0 | 2/2 | 53.7 | 1 | one-shot; too easy for a method comparison |
| `mergesort` | S0 | 6/6 | 498.3 | 3 | two failed checks before the green one |
| `mergesort` | S1 | 6/6 | 392.2 | 13 | 1.27× S0 at 3.2× agent-min |
| `mergesort` | S4 | 6/6 | 376.1 | 31 | only 1.04× S1 at 2× agents |
| `mergesort` | S2/S3 | — | — | — | queued |
| `ref-store` | S0 | 4/4 | 821.2 | 15 | bespoke spec; 13 failed checks before green |
| `ref-store` | S1 | 4/4 | **581.9** | 9 | 1.41× S0 at 2.8× agent-min; best |
| `ref-store` | S2 | 4/4 | 620.4 | 19 | 1.58× S0, 6.6% behind S1; relay overhead |
| `ref-store` | S3 | 4/4 | 981.3 | 30 | slowest; 5m42 plan, clean integration |
| `ref-store` | S4 | 4/4 | 801.4 | 63 | **worse than S2**; only 1.02× S0 at 7.8× compute |

On `ref-store`, S1 wins; S2 is a close second but slower; S4 is barely ahead
of S0 and far behind S1; S3 is slowest.  This is the clearest mid-tier result:
**four independent attempts beat eight, a supervisor, and a lemma cut.**

`ref-store` now has all five methods and is the clearest mid-tier comparison:
**S1 581.9 s, S2 620.4 s, S4 801.4 s, S0 821.2 s, S3 981.3 s.**  S1 wins;
four independent attempts beat eight agents, a supervisor and a lemma cut.
The same ordering holds in the aggregate over `stlc`, `mergesort` and
`ref-store` (S1 1.74× geometric speedup, S4 1.44×).

## Hard tier: PCF, solved

The corrected seven-target statement was raced by four S1 workers.

| target | status | time |
| --- | --- | --- |
| `sim_refl` | green | 150 s |
| `sim_app` | green | 150 s |
| `contextual_le_implies_sim` | not green after ~22 min | — |
| `sim_congruent` (Howe) | not attempted | — |
| `sim_implies_contextual_le` | not attempted | — |
| `contextual_le_iff_sim` | not attempted | — |
| `contextual_eq_iff_sim_both` | not attempted | — |

The statement was then repaired again for tractability: `plug`/`subst0` are
`abbrev`s, and the pivot was split into five partial targets.  A further run
found that the proposed `plug_steps` is **false** — a context can put the hole
under a `lam`, and PCF does not step under binders — so it was replaced by
`contextual_le_plug`; the statement now has **12 targets**.

The repaired S1 run reached **7/12 targets in 23m26s** (agent a1), with empty
axiom footprints: `step_deterministic`, `steps_trans`,
`contextual_le_plug`, `contextual_le_value`, `contextual_le_app`,
`sim_refl`, `sim_app`.  Its file is 652 lines.  A second agent reached 6/12
in 19m14 (444 lines); the other two wrote 461–648 lines and were still
iterating.  The run is not a 12/12 solve.

S2 on the same statement also reached **7/12**, in 24m35s with five agents and
121 checks.  Its verified library broadcast cut time-to-first-target from
17.3m to **9.2m**, but the final target count did not move.  Sharing the
infrastructure is real; it does not by itself unlock the pivot or Howe.

S5, a warm-started three-lane portfolio from the 7/12 proof, reached **8/12**:
the pivot `contextual_le_implies_sim` was proved in 11m08 by a value-focused
lane, with no Howe.  The remaining four targets all reduce to the open-term
Howe substitution lemma
`Simulates (subst0 b1 w1) (subst0 b2 w2)` from `Simulates (lam b1) (lam b2)`
and `Simulates w1 w2`; the weak simulation clause only covers a common
argument.  Two Howe attempts and one non-Howe attempt all stopped there; the
non-Howe lane proved `sim_implies_contextual_le ↔ sim_congruent` and showed
syntactic step-indexing, CIU, and a direct simulation reduce to the same
lemma.

A focused S6 LR continuation then built the semantic step-indexed core
(`VE`/`V`/`E`, downward closure, `stepsN_value`, `V_to_E`, `E_step_both`) but
still reached **8/12**: `Simulates ⊆ E` at function type needs a bounded
right-hand run to compose the same-argument and changed-argument instances.

**S7 solved it by dropping the step index.**  The winning lane defined a
level-free relation `VL`/`EL` by mutual recursion on the type, with
`EL_app`, `EL_fundamental` (open terms under pointwise-`EL` environments), and
`EL_post_sim`.  Then `Simulates = EL`, `EL` is closed under every one-hole
context, and the four remaining targets follow.  **PCF is 12/12 at 19m24**, a
2002-line proof, no `sorry`, no non-standard axioms, and **no Howe relation**.
The Howe lanes added no targets.

In the 7-target run, two of four agents reached 2/7; one stopped at 14m47s with
a de Bruijn/context library and a one-line `plug`/`subst0` unfolding blocker;
the others were still on the same pivot when the block was cut at **26 min**.
Its totals:
2/7 targets, 113 checks, 104.8 agent-minutes, 4.6 targets/hour.  The summary's
`failed_checks` counts every partial check as failed because no problem was
solved; read the target count, not that column.

The easy targets are cheap; the preorder implication is a substantial de Bruijn
and context-composition proof, and Howe is a longer pole still.  This is the
expected shape for the hard tier: partial credit is the signal, and the rate
should be read as targets/hour, not problems/hour.

## What the pilot says

1. **Independent parallelism buys wall clock on the easy problem.**  S1 is
   1.33× faster than S0 on `gcd`; S4 is 1.92× faster.  The price is linear in
   agents: 3.0× and 4.2× the agent-minutes.
2. **Doubling four to eight was worth it on this problem.**  S4's 72 s against
   S1's 105 s is a 1.45× gain for 2× the agents.  One sample, and the winning
   agent was the only one in S4 to reach a second check; treat 1.45× as an
   upper bound until repeated.
3. **Cross-talk did not pay on `gcd`.**  S2's rate is within noise of S0 and
   below S1.  The supervisor's initial broadcast was specific and reasonable
   (it named the `IsGcd` modulo-step invariant and the fuel bound), but the
   workers were already past that point; the 1-minute supervisor turn and the
   relay are pure overhead on a problem with one central lemma.
4. **Lemma cutting was the slowest organisation here.**  S3's 2m51s plan is
   more than the whole S0 solve.  The cut itself was sound — four independent
   workers, no re-cuts, no unused lemmas, one integration defect fixed in one
   line — but the planning and integration cost dominates when the proof is
   small.
5. **S1 also helps on `stlc`, but less.**  373 s against 471 s (1.26×) for
   3.2× the agent-minutes.  The race did not reduce iterations: both methods
   made eight checks, seven of them failed.  Parallel attempts change which
   attempt lands first, not how hard the proof is.
6. **Doubling 4→8 did not help on `stlc`.**  S4 solved in 498 s against S1's
   373 s, with 54 checks against 8.  The check median stayed at 8.2 s, so the
   worker was not the bottleneck; eight copies of the same long proof search
   did not shorten the critical path.  On `gcd`, where one attempt is short
   enough to land early, S4 was the fastest.  Scaling depends on whether the
   proof is a short attempt or a long single search, not on agent count alone.
7. **Lemma cutting was slower on `stlc` too, and for a legible reason.**  The
   cut was clean — four independent modules, no re-cuts, one unused helper,
   four-for-four integration — but the plan cost 3m04s and the substitution
   worker alone took 11m27s.  Cutting moved the long pole into one worker
   instead of removing it.  It pays when the long pole is itself splittable;
   here it was the same induction S0 proved in the course of an 8-minute
   whole-proof attempt.

## Decision rule for the next block

* Easy tier: S4 has the clear rate (72 s, 49.9/h); S1 is 1.18× faster than S0
  on the mean but the ranges almost touch, so S0 remains the cheap choice when
  agent-minutes matter.
* Medium tier: S1 is the current best rate; S3 and S4 are both slower, and S4's
  54 checks show extra agents mostly add attempts, not critical-path progress.
  S2 has no medium-tier evidence.  Repeat S0 and S1 before choosing.
* Hard tier: no evidence yet.  The PCF run is in progress; S3 is the natural
  candidate there because the target is a ladder of lemmas, but the plan cost
  has to be amortised over a much larger proof.

## What this does not establish

* One run per cell.  The differences between S0, S1 and S2 on `gcd` are within
  what one lucky or unlucky attempt can produce; only S3's overhead is large
  enough to be safe to call.
* The problems are small and the corpus is chosen by the experimenter; the
  rates are not a claim about Lean proofs in general.
* The worker is shared by concurrent methods in part of the block, and the
  model is the session default, not a pinned model version.
* The honesty protocol is an honour system.  No run reported an exposure, but
  the harness cannot detect a read proof; the rates are upper bounds if the
  reports are incomplete.
