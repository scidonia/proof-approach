import Std

/-!
# Strong normalisation for the simply typed lambda calculus

Terms use de Bruijn indices.  `Step` is beta reduction together with the two
congruence rules, `SN` is strong normalisation, defined as well-foundedness of
the one-step relation, and `Reducible` is Tait's reducibility candidate.

Nothing here is proved.  Every target is a `Prop`-valued definition, so a proof
module states theorems of exactly those types and the harness compares the two.
-/

namespace Problems.Hard.StlcNorm

/-- Types: one base type and function types. -/
inductive Ty where
  | base : Ty
  | arr : Ty → Ty → Ty
  deriving DecidableEq, Repr

/-- Terms in de Bruijn form: variables, abstraction, application. -/
inductive Tm where
  | var : Nat → Tm
  | lam : Ty → Tm → Tm
  | app : Tm → Tm → Tm
  deriving DecidableEq, Repr

/-- A typing context assigns a type to each de Bruijn index. -/
abbrev Ctx := List Ty

/-- The type assigned to variable `n` by `Γ`, if it is in scope. -/
def lookup (Γ : Ctx) (n : Nat) : Option Ty := Γ[n]?

/-- Add one to every free variable at or above `k`. -/
def shift (k : Nat) : Tm → Tm
  | .var n => if n < k then .var n else .var (n + 1)
  | .lam σ t => .lam σ (shift (k + 1) t)
  | .app t u => .app (shift k t) (shift k u)

/-- Replace variable `j` by `s` and lower the indices above it, which is the
substitution that removes one binder; `s` is shifted under each binder
crossed. -/
def subst (j : Nat) (s : Tm) : Tm → Tm
  | .var n => if n = j then s else if n > j then .var (n - 1) else .var n
  | .lam σ t => .lam σ (subst (j + 1) (shift 0 s) t)
  | .app t u => .app (subst j s t) (subst j s u)

/-- Typing in a context, in the usual de Bruijn style. -/
inductive HasType : Ctx → Tm → Ty → Prop where
  | var {Γ n σ} : lookup Γ n = some σ → HasType Γ (.var n) σ
  | lam {Γ σ t τ} : HasType (σ :: Γ) t τ → HasType Γ (.lam σ t) (.arr σ τ)
  | app {Γ t u σ τ} :
      HasType Γ t (.arr σ τ) → HasType Γ u σ → HasType Γ (.app t u) τ

/-- One step of beta reduction, closed under the two application positions. -/
inductive Step : Tm → Tm → Prop where
  | beta {σ t u} : Step (.app (.lam σ t) u) (subst 0 u t)
  | app₁ {t t' u} : Step t t' → Step (.app t u) (.app t' u)
  | app₂ {t u u'} : Step u u' → Step (.app t u) (.app t u')

/-- Reflexive-transitive closure of `Step`. -/
inductive Steps : Tm → Tm → Prop where
  | refl (t) : Steps t t
  | step {t u v} : Step t u → Steps u v → Steps t v

/-- Strong normalisation: the one-step relation is well founded at `t`. -/
def SN (t : Tm) : Prop := Acc (fun u v => Step v u) t

/-- Tait's reducibility candidate.  At the base type it is strong normalisation;
at a function type a term is reducible when it maps reducible arguments to
reducible applications. -/
def Reducible : Ty → Tm → Prop
  | .base, t => SN t
  | .arr σ τ, t => ∀ u, Reducible σ u → Reducible τ (.app t u)

/-- Target: a strongly normalising term has strongly normalising reducts. -/
def sn_step : Prop := ∀ {t u : Tm}, SN t → Step t u → SN u

/-- Target: every reducible term is strongly normalising. -/
def reducible_sn : Prop := ∀ (σ : Ty) (t : Tm), Reducible σ t → SN t

/-- Target: every closed term of type `σ` is reducible. -/
def reducible_closed : Prop := ∀ (σ : Ty) (t : Tm), HasType [] t σ → Reducible σ t

/-- Target: every well-typed closed term is strongly normalising. -/
def strong_normalisation : Prop := ∀ (σ : Ty) (t : Tm), HasType [] t σ → SN t

end Problems.Hard.StlcNorm
