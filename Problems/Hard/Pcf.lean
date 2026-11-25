import Std

/-!
# PCF: contextual preorder and applicative similarity

A call-by-value PCF: `nat`, `bool`, function types, de Bruijn indices, and a
`fix` combinator.  The operational semantics is a small-step relation on closed
terms.  `ContextualLe` is one-directional may-testing through every one-hole
context; `ContextualEq` is its symmetrisation.  `Simulates` is the union of all
applicative simulations.

The standard result is that `ContextualLe` and `Simulates` coincide, and hence
that contextual equivalence is similarity in both directions.  The hard
direction is that similarity is a congruence, which is Howe's method; the
targets below expose that direction as its own declaration so a proof that gets
only part of the way is scored for the part.

A one-directional `IsSimulation` is deliberately not called a bisimulation:
`omega = fix (fun x => x)` simulates `zero` (the simulation clause never
demands a matching divergence), while `zero` does not simulate `omega`, and
they are not contextually equivalent.  The equivalence is recovered by
requiring similarity in both directions in `contextual_eq_iff_sim_both`.

This file contains definitions and targets only.  No target is proved here.
-/

namespace Problems.Hard.Pcf

inductive Ty where
  | nat : Ty
  | bool : Ty
  | arr : Ty → Ty → Ty

inductive Var : List Ty → Ty → Type where
  | here : Var (σ :: Γ) σ
  | there : Var Γ σ → Var (τ :: Γ) σ

inductive Tm : List Ty → Ty → Type where
  | var : Var Γ σ → Tm Γ σ
  | lam : Tm (σ :: Γ) τ → Tm Γ (Ty.arr σ τ)
  | app : Tm Γ (Ty.arr σ τ) → Tm Γ σ → Tm Γ τ
  | zero : Tm Γ Ty.nat
  | succ : Tm Γ Ty.nat → Tm Γ Ty.nat
  | pred : Tm Γ Ty.nat → Tm Γ Ty.nat
  | ifz : Tm Γ Ty.nat → Tm Γ σ → Tm Γ σ → Tm Γ σ
  | tt : Tm Γ Ty.bool
  | ff : Tm Γ Ty.bool
  | cond : Tm Γ Ty.bool → Tm Γ σ → Tm Γ σ → Tm Γ σ
  | fix : Tm Γ (Ty.arr σ σ) → Tm Γ σ

/-- Lift a variable renaming under a binder. -/
def liftRen {Γ Δ : List Ty} {τ : Ty}
    (ρ : ∀ {σ}, Var Γ σ → Var Δ σ) : ∀ {σ}, Var (τ :: Γ) σ → Var (τ :: Δ) σ
  | _, .here => .here
  | _, .there w => .there (ρ w)

/-- Renaming of de Bruijn variables. -/
def rename : (∀ {σ}, Var Γ σ → Var Δ σ) → Tm Γ τ → Tm Δ τ
  | ρ, .var v => .var (ρ v)
  | ρ, .lam b => .lam (rename (liftRen ρ) b)
  | ρ, .app f a => .app (rename ρ f) (rename ρ a)
  | _, .zero => .zero
  | ρ, .succ t => .succ (rename ρ t)
  | ρ, .pred t => .pred (rename ρ t)
  | ρ, .ifz n t e => .ifz (rename ρ n) (rename ρ t) (rename ρ e)
  | _, .tt => .tt
  | _, .ff => .ff
  | ρ, .cond b t e => .cond (rename ρ b) (rename ρ t) (rename ρ e)
  | ρ, .fix f => .fix (rename ρ f)

/-- Lift a substitution under a binder. -/
def liftSubst {Γ Δ : List Ty} {τ : Ty}
    (σs : ∀ {σ}, Var Γ σ → Tm Δ σ) :
    ∀ {σ}, Var (τ :: Γ) σ → Tm (τ :: Δ) σ
  | _, .here => .var .here
  | _, .there w => rename (fun x => .there x) (σs w)

/-- Substitution of de Bruijn variables. -/
def subst : (∀ {σ}, Var Γ σ → Tm Δ σ) → Tm Γ τ → Tm Δ τ
  | σs, .var v => σs v
  | σs, .lam b => .lam (subst (liftSubst σs) b)
  | σs, .app f a => .app (subst σs f) (subst σs a)
  | _, .zero => .zero
  | σs, .succ t => .succ (subst σs t)
  | σs, .pred t => .pred (subst σs t)
  | σs, .ifz n t e => .ifz (subst σs n) (subst σs t) (subst σs e)
  | _, .tt => .tt
  | _, .ff => .ff
  | σs, .cond b t e => .cond (subst σs b) (subst σs t) (subst σs e)
  | σs, .fix f => .fix (subst σs f)

/-- The substitution that replaces the innermost variable by `a`. -/
def substHere {Γ : List Ty} {σ : Ty} (a : Tm Γ σ) :
    ∀ {υ : Ty}, Var (σ :: Γ) υ → Tm Γ υ
  | _, .here => a
  | _, .there w => .var w

/-- Substitute a closed term for the innermost variable. -/
abbrev subst0 {Γ : List Ty} {σ τ : Ty} (b : Tm (σ :: Γ) τ) (a : Tm Γ σ) : Tm Γ τ :=
  subst (substHere a) b

/-- Values: the closed canonical forms. -/
inductive Value : Tm [] σ → Prop where
  | zero : Value .zero
  | tt : Value .tt
  | ff : Value .ff
  | lam : Value (.lam b)
  | succ : Value t → Value (.succ t)

/-- Call-by-value small-step reduction on closed terms. -/
inductive Step : Tm [] σ → Tm [] σ → Prop where
  | succ : Step t t' → Step (.succ t) (.succ t')
  | pred_zero : Step (.pred .zero) .zero
  | pred_succ : Value v → Step (.pred (.succ v)) v
  | pred : Step t t' → Step (.pred t) (.pred t')
  | ifz_zero : Step (.ifz .zero t e) t
  | ifz_succ : Value v → Step (.ifz (.succ v) t e) e
  | ifz : Step n n' → Step (.ifz n t e) (.ifz n' t e)
  | cond_tt : Step (.cond .tt t e) t
  | cond_ff : Step (.cond .ff t e) e
  | cond : Step b b' → Step (.cond b t e) (.cond b' t e)
  | app_lam : Value v → Step (.app (.lam b) v) (subst0 b v)
  | app_fun : Step f f' → Step (.app f a) (.app f' a)
  | app_arg : Value f → Step a a' → Step (.app f a) (.app f a')
  | fix : Step (.fix f) (.app f (.fix f))

/-- Reflexive-transitive closure of `Step`. -/
inductive Steps {σ : Ty} : Tm [] σ → Tm [] σ → Prop where
  | refl (t : Tm [] σ) : Steps t t
  | step {t u v : Tm [] σ} : Steps t u → Step u v → Steps t v

/-- A closed term terminates when it reaches a value. -/
def Terminates {σ : Ty} (t : Tm [] σ) : Prop := ∃ v, Value v ∧ Steps t v

/-- Plug a closed term into a one-hole context.  A context is a term with one
free variable of the hole's type.  `abbrev` so `plug` unfolds in a `rw`/`simp`
without a separate equation lemma. -/
abbrev plug {σ τ : Ty} (C : Tm [σ] τ) (t : Tm [] σ) : Tm [] τ := subst0 C t

/-- One-directional may-testing: every context that terminates on `t` also
terminates on `u`. -/
def ContextualLe {σ : Ty} (t u : Tm [] σ) : Prop :=
  ∀ {τ : Ty} (C : Tm [σ] τ), Terminates (plug C t) → Terminates (plug C u)

/-- Contextual equivalence: may-testing in both directions. -/
def ContextualEq {σ : Ty} (t u : Tm [] σ) : Prop :=
  ContextualLe t u ∧ ContextualLe u t

/-- The applicative simulation clause.  At `nat` and `bool` the matched values
must be **equal**: relating `zero` to `succ zero` would claim
`Simulates zero (succ zero)`, which the context `ifz □ 0 omega` refutes.  At a
function type the matched values are related by `R` and the relation contains
the application clause for every closed argument. -/
def IsSimulation (R : ∀ {σ : Ty}, Tm [] σ → Tm [] σ → Prop) : Prop :=
  (∀ (t u : Tm [] Ty.nat), R t u →
      ∀ v, Value v → Steps t v → ∃ v', Value v' ∧ Steps u v' ∧ v = v')
  ∧ (∀ (t u : Tm [] Ty.bool), R t u →
      ∀ v, Value v → Steps t v → ∃ v', Value v' ∧ Steps u v' ∧ v = v')
  ∧ (∀ {σ τ : Ty} (t u : Tm [] (Ty.arr σ τ)), R t u →
      (∀ v, Value v → Steps t v → ∃ v', Value v' ∧ Steps u v' ∧ R v v')
      ∧ (∀ a : Tm [] σ, R (.app t a) (.app u a)))

/-- Applicative similarity: the union of all applicative simulations. -/
def Simulates {σ : Ty} (t u : Tm [] σ) : Prop :=
  ∃ R, IsSimulation R ∧ R t u

/-! ## Targets -/

/-- Target: one step is deterministic. -/
def step_deterministic : Prop :=
  ∀ {σ : Ty} {t u v : Tm [] σ}, Step t u → Step t v → u = v

/-- Target: `Steps` is transitive. -/
def steps_trans : Prop :=
  ∀ {σ : Ty} {t u v : Tm [] σ}, Steps t u → Steps u v → Steps t v

/-- Target: the contextual may-preorder is closed under plugging both sides
into the same context.  (Reduction itself is not preserved by an arbitrary
context: a context can put the hole under a `lam`, and PCF does not step under
binders.  This is the closure property the proof actually uses.) -/
def contextual_le_plug : Prop :=
  ∀ {σ τ : Ty} (C : Tm [σ] τ) {t u : Tm [] σ},
    ContextualLe t u → ContextualLe (plug C t) (plug C u)

/-- Target: values reached from contextually related terms are contextually
related.  This is the value half of `contextual_le_implies_sim`. -/
def contextual_le_value : Prop :=
  ∀ {σ : Ty} (t u v v' : Tm [] σ),
    ContextualLe t u → Value v → Steps t v → Value v' → Steps u v' →
    ContextualLe v v'

/-- Target: applying contextually related functions to the same argument
preserves the contextual preorder.  This is the application half of
`contextual_le_implies_sim`. -/
def contextual_le_app : Prop :=
  ∀ {σ τ : Ty} (t u : Tm [] (Ty.arr σ τ)) (a : Tm [] σ),
    ContextualLe t u → ContextualLe (.app t a) (.app u a)

/-- Every term simulates itself. -/
def sim_refl : Prop := ∀ {σ : Ty} (t : Tm [] σ), Simulates t t

/-- Similarity is preserved by applying both sides to the same argument. -/
def sim_app : Prop :=
  ∀ {σ τ : Ty} (t u : Tm [] (Ty.arr σ τ)) (a : Tm [] σ),
    Simulates t u → Simulates (.app t a) (.app u a)

/-- Contextual may-preorder implies applicative similarity. -/
def contextual_le_implies_sim : Prop :=
  ∀ {σ : Ty} (t u : Tm [] σ), ContextualLe t u → Simulates t u

/-- Similarity is a precongruence: under every one-hole context, similar terms
remain similar.  This is the direction that needs Howe's method. -/
def sim_congruent : Prop :=
  ∀ {σ τ : Ty} (C : Tm [σ] τ) (t u : Tm [] σ),
    Simulates t u → Simulates (plug C t) (plug C u)

/-- Applicative similarity implies the contextual may-preorder. -/
def sim_implies_contextual_le : Prop :=
  ∀ {σ : Ty} (t u : Tm [] σ), Simulates t u → ContextualLe t u

/-- The preorder equivalence: contextual may-testing and applicative
similarity coincide. -/
def contextual_le_iff_sim : Prop :=
  ∀ {σ : Ty} (t u : Tm [] σ), ContextualLe t u ↔ Simulates t u

/-- The equivalence: contextual equivalence is similarity in both directions.
This is the statement the pilot's one-directional `IsBisimulation` got wrong:
`omega` simulates `zero` but not conversely, so one direction alone is not
contextual equivalence. -/
def contextual_eq_iff_sim_both : Prop :=
  ∀ {σ : Ty} (t u : Tm [] σ),
    ContextualEq t u ↔ (Simulates t u ∧ Simulates u t)

end Problems.Hard.Pcf
