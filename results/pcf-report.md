# PCF: repair, retry, and completion

**Status: 12/12 targets green. Solved.** The winning lane is a **level-free
logical relation**, not Howe. The proof is 2002 lines, with no `sorry` and no
non-standard axioms.

| fact | value |
| --- | --- |
| problem | call-by-value PCF: contextual may-preorder ↔ applicative similarity, equivalence both ways |
| targets | 12/12 |
| winning method | S7 focused block, lane `a3`, level-free LR |
| solve time | 19m24s from the 3-lane start |
| agents in block | 3 (two Howe lanes, one LR lane) |
| checks | 15 |
| agent-minutes | 63.6 |
| proof size | 2002 lines |

## 1. The statement was repaired three times

The first PCF statement was not merely hard; it was wrong in three ways.

| defect | how it was found | repair |
| --- | --- | --- |
| a union of **one-directional** relations called a bisimulation | an agent proved `omega` simulates `zero` | one-directional `Simulates`; equivalence is similarity both ways |
| ground values compared by the relation itself | an agent refuted `zero ~ succ zero` via `ifz □ 0 omega` | ground clauses require value equality |
| proposed sub-target `plug_steps` (“contexts preserve reduction”) | three agents found it false: a context can put the hole under a `lam`, and PCF does not step under binders | replaced by `contextual_le_plug` |

Two proof-engineering repairs: `plug`/`subst0` are `abbrev`s, and the pivot
was split so partial work is scored.  The final statement has 12 targets.

## 2. The final proof route

The obstruction was the **step index**, not the relation.  A bound on the left
computation loses a level at every application: the same-argument instance from
`Simulates` and the changed-argument instance from the fundamental theorem
cannot be composed, because `E`’s right-hand run is unbounded.  Strict and
non-strict level variants both fail (one breaks the application case, the other
the strong induction).

The winning lane dropped the index.  `EL`/`VL` are defined by mutual recursion
on the type only:

```
EL τ t t' := ∀ v, Value v → Steps t v →
               ∃ v', Value v' ∧ Steps t' v' ∧ VL τ v v'

VL (arr σ τ) v v' := ∀ a a', Value a → Value a' → VL σ a a' →
                       EL τ (app v a) (app v' a')
```

The three pieces that replace the missing composition:

1. `EL_app` — `EL` is closed under application of related parts, using
   `stepsN_app_inv` and `VL_arr`.
2. `EL_fundamental` — open terms under pointwise-`EL` closing environments, by
   structural induction on the term; the lambda case uses `subst_envCons`,
   `fix` uses cumulative induction on the `StepsN` bound.
3. `EL_post_sim` — `EL τ t u → Simulates u s → EL τ t s`; at function type the
   changed argument on the right is supplied by `VL_arr` itself.

Then `Simulates ⊆ EL` (the formerly blocked arrow case is discharged by the
fundamental theorem plus `EL_post_sim`), `EL` is a simulation, so
`Simulates = EL`; `EL` is closed under every one-hole context by the
fundamental theorem at the context; hence `sim_congruent`.  Targets 10–12
follow from the pre-existing assemblies.

**There is no Howe relation in the final proof.** The attempt is genuinely
non-Howe: a level-free logical relation with an open-term fundamental theorem.

## 3. Method results

| stage | best | notes |
| --- | ---: | --- |
| cold S1 | 7/12 | 4 agents, first target 17.3m, 95 checks |
| cold S2 | 7/12 | 5 agents, shared-library broadcast cut first target to 9.2m |
| S5 warm portfolio | 8/12 | 3 agents from the 7/12 base; pivot green in 11m08 |
| **S7 focused block** | **12/12** | 3 agents from 8/12 bases; LR lane solved in 19m24 |

The warm start was decisive: cold runs stalled at 7/12 rebuilding the same
400–650-line substitution library; from the verified base, the pivot fell in
11 minutes and the final LR route in another 19.

## 4. What failed, and why it mattered

Two Howe lanes and several earlier attempts reduced the hard direction to the
changed-argument substitution lemma:

```
Simulates (lam b) (lam b') →
  ∀ w w', Value w → Value w' → Simulates w w' →
    Simulates (subst0 b w) (subst0 b' w')
```

The weak simulation clause only supplies the **same** argument.  A closed-term
Howe relation reaches a `lam` pair only via its base rule, which carries no
body information, so the `lam` rule is not invertible.  The syntactic
step-indexed relation and CIU routes either circularise or bottom out in the
same lemma.  The level-free LR avoids the composition rather than proving it.

A separate correction: arbitrary one-step reduction closure of a Howe
relation, `Howe t u → Step t t' → ∃ u', Steps u u' ∧ Howe t' u'`, is false
for `(omega, zero)`; the simulation property must be proved by evaluation
induction, not arbitrary step closure.

## 5. Lessons

1. **Warm start beats agent count on hard problems.** Cold S1/S2: 7/12. Warm
   S5: 8/12. Focused S7: 12/12. The shared prerequisite was the infrastructure,
   not the theorem.
2. **Granularity gives signal.** 7/12 → 8/12 → 12/12 was measurable because
   the pivot and the LR layers were separate targets.
3. **A route can be non-Howe, but not cheap.** The LR route needed a
   level-free reformulation and an open-term fundamental theorem.  It is not a
   shortcut; it is a different proof.
4. **The step index was the wrong abstraction.** The obstruction vanished when
   the index was dropped; `EL_app`/`EL_fundamental`/`EL_post_sim` supply the
   composition.
5. **Multiple agents help by diversity of routes, not by raw count.** The LR
   lane and the Howe lanes started from different 8/12 bases; the LR lane won.
   The two Howe lanes added no targets.

## 6. Caveats

- One solved run.  The 12/12 is kernel-checked, but the method comparison is
  one sample; S7 is a 3-agent warm block, not a cold method.
- The winning proof is 2002 lines and depends on the earlier 8/12 library; it
  is not a from-scratch cold proof.
- The two Howe lanes did not finish; their scaffolding and the exact blocked
  obligation remain in their workspaces.
- The worker was deleted after the block.
- The theorem is known, not new: applicative bisimulation is fully abstract for
  cbv PCF (Koutavas–Levy–Sumii 2011; Howe 1996; see `docs/pcf.md`).  The run
  measures proof production, not a new mathematical result.

## 7. Artifacts

- `Problems/Hard/Pcf.lean` — the 12-target statement.
- `runs/s7-pcf-final/agents/a3/workspace/Proofs/Hard/Pcf.lean` — the 12/12 proof.
- `runs/s7-pcf-final/summary.json` — solve time, targets, checks.
- `docs/pcf.md` — formalisation, repair history and the final route.
- `results/README.md`, `results/index-and-speedup.md` — broader method results.

## Bottom line

PCF is **solved**: 12/12, no axioms, by a **non-Howe level-free logical
relation**.  The path was: repair the statement three times, warm-start from
7/12, clear the pivot non-Howe, then drop the step index and prove the
fundamental theorem over open-term environments.  Howe was not necessary.
