import Std

/-!
# Simply typed lambda calculus

Terms are untyped de Bruijn syntax and typing is extrinsic: `HasType Γ t A`
relates an untyped term to a type in a context.  The operational semantics is
call-by-value, and the targets are the usual metatheory: preservation of typing
under substitution, progress, preservation, and determinism of the step
relation.
-/

namespace Problems.Medium.Stlc

/-- Types: a single base type and function types. -/
inductive Ty where
  | base : Ty
  | arr : Ty → Ty → Ty

/-- Untyped terms in de Bruijn form.  `lam` carries the type of its argument
because typing is extrinsic. -/
inductive Tm where
  | var : Nat → Tm
  | lam : Ty → Tm → Tm
  | app : Tm → Tm → Tm
  | zero : Tm
  | succ : Tm → Tm

/-- A context is a list of types, innermost binder first. -/
abbrev Ctx := List Ty

/-- Extrinsic typing: `HasType Γ t A` says `t` has type `A` in context `Γ`.
A variable is typed by looking its de Bruijn index up in the context. -/
inductive HasType : Ctx → Tm → Ty → Prop where
  | var {Γ : Ctx} {n : Nat} {A : Ty} : Γ[n]? = some A → HasType Γ (.var n) A
  | lam {Γ : Ctx} {A B : Ty} {t : Tm} :
      HasType (A :: Γ) t B → HasType Γ (.lam A t) (.arr A B)
  | app {Γ : Ctx} {A B : Ty} {f a : Tm} :
      HasType Γ f (.arr A B) → HasType Γ a A → HasType Γ (.app f a) B
  | zero {Γ : Ctx} : HasType Γ .zero .base
  | succ {Γ : Ctx} {t : Tm} : HasType Γ t .base → HasType Γ (.succ t) .base

/-- Shift the free variables of a term that are at or above `k` up by one. -/
def shift (k : Nat) : Tm → Tm
  | .var n => if n < k then .var n else .var (n + 1)
  | .lam A t => .lam A (shift (k + 1) t)
  | .app f a => .app (shift k f) (shift k a)
  | .zero => .zero
  | .succ t => .succ (shift k t)

/-- Substitute `s` for the variable with index `j`, decrementing the indices
above `j` so that the removed binder closes up.  Going under a binder shifts
`s` to keep the substitution capture-avoiding. -/
def subst (j : Nat) (s : Tm) : Tm → Tm
  | .var n => if n < j then .var n else if n = j then s else .var (n - 1)
  | .lam A t => .lam A (subst (j + 1) (shift 0 s) t)
  | .app f a => .app (subst j s f) (subst j s a)
  | .zero => .zero
  | .succ t => .succ (subst j s t)

/-- The values of the call-by-value semantics: lambdas, `zero`, and successors
of values. -/
inductive Value : Tm → Prop where
  | lam (A : Ty) (t : Tm) : Value (.lam A t)
  | zero : Value .zero
  | succ {t : Tm} : Value t → Value (.succ t)

/-- Call-by-value, left-to-right single step.  `beta` substitutes the argument
for the outermost variable of the body and closes up the context. -/
inductive Step : Tm → Tm → Prop where
  | beta {A : Ty} {body arg : Tm} :
      Value arg → Step (.app (.lam A body) arg) (subst 0 arg body)
  | app_fun {f f' a : Tm} : Step f f' → Step (.app f a) (.app f' a)
  | app_arg {f a a' : Tm} : Value f → Step a a' → Step (.app f a) (.app f a')
  | succ {t t' : Tm} : Step t t' → Step (.succ t) (.succ t')

/-- Reflexive-transitive closure of `Step`. -/
inductive Steps : Tm → Tm → Prop where
  | refl (t : Tm) : Steps t t
  | step {t u v : Tm} : Step t u → Steps u v → Steps t v

/-- A term terminates if it reaches a value. -/
def Terminates (t : Tm) : Prop := ∃ v, Value v ∧ Steps t v

/-- Target: substituting a well-typed term for the variable at the split point
of `Γ₁ ++ A :: Γ₂` preserves typing. -/
def subst_preserves_typing : Prop :=
  ∀ (Γ₁ : Ctx) (A : Ty) (t : Tm) (Γ₂ : Ctx) (u : Tm) (B : Ty),
    HasType Γ₁ t A → HasType (Γ₁ ++ A :: Γ₂) u B →
      HasType (Γ₁ ++ Γ₂) (subst Γ₁.length t u) B

/-- Target: a closed well-typed term is a value or takes a step. -/
def progress : Prop := ∀ (t : Tm) (A : Ty), HasType [] t A → Value t ∨ ∃ t', Step t t'

/-- Target: a closed well-typed term steps only to a term of the same type. -/
def preservation : Prop :=
  ∀ (t t' : Tm) (A : Ty), HasType [] t A → Step t t' → HasType [] t' A

/-- Target: `Step` is deterministic. -/
def deterministic : Prop := ∀ (t u v : Tm), Step t u → Step t v → u = v

end Problems.Medium.Stlc
