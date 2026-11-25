# The PCF problem

`Problems/Hard/Pcf.lean` formalises call-by-value PCF and states the standard
result that the contextual may-preorder and applicative similarity coincide,
and that contextual equivalence is similarity in both directions.  It is the
hard end of the corpus: the theorem is known but the proof is research-level,
and it is a ladder, so a partial proof is scored.

## Syntax and semantics

* Types: `nat`, `bool`, `arr σ τ`.
* Terms: de Bruijn indices, `lam`, `app`, `zero`, `succ`, `pred`, `ifz`, `tt`,
  `ff`, `cond`, `fix`.  Terms are intrinsically scoped: `Tm Γ σ`.
* `Value`: `zero`, `tt`, `ff`, `lam`, and `succ` of a value.
* `Step`: call-by-value, left-to-right small step on closed terms.  `fix f`
  unfolds to `app f (fix f)`; beta substitutes the argument for the innermost
  variable.
* `Steps`: reflexive-transitive closure; `Terminates t` means `t` reaches a
  value.

## The relations

`ContextualLe t u` quantifies over every one-hole context `C : Tm [σ] τ` and
requires `Terminates (plug C t) → Terminates (plug C u)`.  A context is a term
with one free variable; `plug` substitutes the closed term for it.
`ContextualEq t u` is `ContextualLe t u ∧ ContextualLe u t`.

`Simulates t u` is the union of all applicative simulations.  A relation `R` is
a simulation when, at `nat` and `bool`, `R t u` implies the termination clause
with **value equality** — every value `t` reaches, `u` reaches the same value —
and at a function type it implies both the termination clause with `R` on the
matched values and the application clause `R (app t a) (app u a)` for every
closed `a`.  Value equality at ground types is load-bearing: a clause that
merely requires the matched values to be `R`-related relates `zero` to
`succ zero`, which the context `ifz □ 0 omega` refutes.

## Literature status

The theorem is known, not new.  Applicative bisimulation is fully abstract for
call-by-value PCF: Koutavas, Levy and Sumii, *From applicative to environmental
bisimulation* (MFPS 2011), and Howe, *Proving congruence of bisimulation in
functional programming languages* (1996).  Koutavas, Lin and Tzevelekos,
*Fully Abstract Normal Form Bisimulation for Call-by-Value PCF* (LICS 2023),
state it explicitly — “Using the fact that applicative bisimulation is fully
abstract [15],[11]” — and their novelty is a **normal form** bisimulation, a
different relation, not the first fully abstract operational model for PCFv.
The logical-relations characterisation is also classical (Pitts 1998/2002;
O'Hearn and Riecke 1995).

What this repository adds is a Lean 4 formalisation and a non-Howe, level-free
logical-relation proof route, not a new theorem.  Do not claim the theorem or
the `EL`/`VL` relation as new mathematics.

## Why similarity, not bisimulation-by-union

The relation is deliberately one-directional.  A union of one-directional
simulations is not a bisimulation: the relation "`t` diverges and `u` is
arbitrary" satisfies the simulation clause at `nat` (the premise never fires),
so `omega = fix (fun x => x)` simulates `zero`.  `zero` does not simulate
`omega`, and the two are not contextually equivalent.  A statement that calls
the union a bisimulation and concludes contextual *equivalence* from it in one
direction is false.

The equivalence is recovered by requiring similarity both ways, which is the
last target.  This is the standard may-testing formulation; the pilot run
before the correction is what found the error.

## Targets

| target | what it is | why it is true |
| --- | --- | --- |
| `step_deterministic` | one step has one result | case analysis on the rules |
| `steps_trans` | `Steps` composes | the closure's induction |
| `contextual_le_plug` | the preorder is closed under a context | nested contexts compose; reduction itself is *not* preserved under a `lam` |
| `contextual_le_value` | values reached from related terms are related | test contexts separate the canonical forms |
| `contextual_le_app` | related functions stay related under an argument | `app · a` is a context |
| `sim_refl` | reflexivity | equality is a simulation |
| `sim_app` | the applicative clause | the witnessing relation already contains the applications |
| `contextual_le_implies_sim` | the contextual preorder is a simulation | context closure: `app · a` and the termination observation are contexts; the value case forces the two values into the relation |
| `sim_congruent` | similarity is a precongruence | Howe's method; the hard direction |
| `sim_implies_contextual_le` | a precongruent similarity is below the contextual preorder | for each context, congruence gives similarity of the plugged terms, and the termination clause gives the observation |
| `contextual_le_iff_sim` | the preorder equivalence | the two implications |
| `contextual_eq_iff_sim_both` | contextual equivalence is similarity both ways | `ContextualEq` is the symmetrisation of `ContextualLe` |

`sim_congruent` is the declaration that carries the research content.  A proof
that establishes only the first three targets is scored for three; the harness
does not require the flagship theorem for partial credit.

**Rerun result:** `contextual_le_value` *is* independently provable.  One
agent proved it in 23 minutes without Howe, via value-normal-form uniqueness
(`steps_prefix` + `steps_value_self`) and the context `(λ.D) □`.  Another
agent’s route appeared to need Howe, but that was a local strategy limitation,
not a dependency.  The hard remaining steps are
`contextual_le_implies_sim` — which additionally needs the ground-value
discriminating contexts (`ifz`/`cond` towers) to upgrade “some value” to “the
same value” — and `sim_congruent` (Howe).  Targets 10–12 follow from those.

## Repair history

The first version called the union of one-directional simulations a
bisimulation; an agent refuted the equivalence with `omega` and `zero`.  A
second version related ground values by the relation itself; an agent refuted
it with `zero` and `succ zero` via `ifz □ 0 omega`.  The current version uses

- one-directional `Simulates` for the preorder,
- **equality** at `nat`/`bool`, which is observational here because the
  language has no opaque literal constructor (the only nat values are `zero`
  and `succ v`; `ifz` separates zero from successor and `pred` peels
  successors),
- contextual equivalence as similarity both ways.

Two proof-engineering repairs accompany the statement:

- `subst0` and `plug` are `abbrev`, so a `rw`/`simp` unfolds them instead of
  stopping at the wrapper.
- The pivot `contextual_le_implies_sim` is split into five smaller targets:
  `step_deterministic`, `steps_trans`, `contextual_le_plug`,
  `contextual_le_value` and `contextual_le_app`.  The full implication remains
  a target, but partial work is scored.
- `plug_steps` was proposed and **refuted by the workers**: a context can put
  the hole under a `lam`, and PCF does not step under binders.  Context
  *closure* of the preorder is the true property, so it replaces it.

## Why this shape

* **Call-by-value, not call-by-name.**  The semantics has the usual cbv redex
  order; the value restriction appears in beta.  The result is the standard
  applicative-similarity full-abstraction theorem for cbv PCF (Koutavas,
  Levy, Sumii 2011; Howe 1996).  Abramsky's lazy lambda calculus is the
  call-by-name variant; this is not that theorem.
* **May-testing at every type.**  `ContextualLe` observes termination at the
  result type rather than only at `bool`.  This is the usual may-testing
  preorder presented uniformly: for any type, a context `(fun _ => tt) □`
  observes termination at `bool`, so the extra result types add no power.
* **A union of simulations.**  `Simulates` is the union of all relations
  satisfying the clause, i.e. the greatest fixpoint in this setting, without a
  coinduction principle the corpus would otherwise have to build.
* **No step indexing.**  The statement is the plain preorder; a step-indexed
  logical relation is a different proof of the same theorem, not a different
  statement.

## A cut for the lemma-cutting method

A supervisor that wants independent lemmas can use:

1. `step_deterministic` and `steps_deterministic` (needed by the easy
   direction to identify the value `u` reaches).
2. `plug_subst` / context composition: `plug (compose C D) t = plug C (plug D t)`
   and `plug C` preserves `Steps`.
3. `contextual_le_is_simulation` (the body of target 3).
4. Howe's relation `≲`, its precongruence lemmas, and `≲ ⊆ Simulates` and
   `Simulates ⊆ ≲`.
5. The three assemblies.

The dependency graph is deep; a cut that assigns (1) and (2) to one worker and
(3) to another is real parallelism, but (4) is a single long pole and does not
cut usefully without the intermediate Howe lemmas.

## Known pitfalls

* De Bruijn substitution under binders must shift the substituted term; the
  statement file's `subst0` does this, but a helper that re-implements it will
  diverge.
* `fix` unfolds at every type; the function case of a simulation must cover
  `fix f` as a function-typed term, not only `lam`.
* `Value` is indexed by `Tm [] σ`; a `succ` of a value is a value, which the
  progress-like arguments need.
* A context is a `Tm [σ] τ`, not a function; `plug` is substitution, and
  composing contexts is a substitution lemma.
* Do not strengthen one direction of a simulation into a bisimulation.  The
  `omega`/`zero` pair is the counterexample.
* Do not compare ground values by the relation alone.  `zero` and `succ zero`
  are both values; relating them makes `ifz □ 0 omega` a counterexample to the
  contextual-preorder implication.  Ground clauses require equality.

## Completion

All 12 targets are green.  The winning route is **non-Howe**: a level-free
logical relation, not a Howe relation.

```
EL τ t t' := ∀ v, Value v → Steps t v →
               ∃ v', Value v' ∧ Steps t' v' ∧ VL τ v v'

VL (arr σ τ) v v' := ∀ a a', Value a → Value a' → VL σ a a' →
                       EL τ (app v a) (app v' a')
```

The composition that the step-indexed relation could not make is supplied by
three lemmas: `EL_app` (application closure), `EL_fundamental` (open terms
under pointwise-`EL` closing environments, by structural induction), and
`EL_post_sim` (`EL` is closed under `Simulates` on the right).  Then
`Simulates ⊆ EL`, `EL` is a simulation, so `Simulates = EL`; `EL` is closed
under one-hole contexts by the fundamental theorem, giving `sim_congruent`.
Targets 10–12 follow from the existing assemblies.

The decisive repair was to **drop the step index**.  A bound on the left
computation loses a level at every application; strict and non-strict variants
both fail.  The level-free relation avoids the composition rather than proving
the changed-argument substitution lemma.

Measured: S7 lane `a3`, 19m24s from a 3-lane warm start, 2002-line proof, no
`sorry`, no non-standard axioms.

