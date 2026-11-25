import Std

/-!
# A dependently typed language: `Nat` and vectors

Adapted from the `dep_vec` challenge in `rocq-piler`'s incomplete benchmark
corpus.  Types are `Nat` and `Vec n`; terms include literals, successors,
vector construction, head and tail.  Typing is extrinsic; the two targets are
the standard preservation and progress theorems for the small-step semantics.

The source benchmark presents each theorem together with its negation and asks
for exactly one of the pair.  The positive forms are the ones stated here; the
negations are not targets.
-/

namespace Problems.Medium.DepVec

inductive Ty where
  | nat : Ty
  | vec : Nat → Ty

inductive Tm where
  | zero : Tm
  | succ : Tm → Tm
  | lit : Nat → Tm
  | nil : Tm
  | cons : Tm → Tm → Tm
  | head : Tm → Tm
  | tail : Tm → Tm

/-- Extrinsic typing. -/
inductive HasType : Tm → Ty → Prop where
  | zero : HasType .zero .nat
  | succ : HasType t .nat → HasType (.succ t) .nat
  | lit : HasType (.lit n) .nat
  | nil : HasType .nil (.vec 0)
  | cons : HasType hd .nat → HasType tl (.vec n) →
      HasType (.cons hd tl) (.vec (n + 1))
  | head : HasType v (.vec (n + 1)) → HasType (.head v) .nat
  | tail : HasType v (.vec (n + 1)) → HasType (.tail v) (.vec n)

/-- Canonical forms. -/
inductive Value : Tm → Prop where
  | zero : Value .zero
  | succ : Value t → Value (.succ t)
  | lit : Value (.lit n)
  | nil : Value .nil
  | cons : Value hd → Value tl → Value (.cons hd tl)

/-- Call-by-value small step. -/
inductive Step : Tm → Tm → Prop where
  | succ : Step t t' → Step (.succ t) (.succ t')
  | consHd : Step hd hd' → Step (.cons hd tl) (.cons hd' tl)
  | consTl : Value hd → Step tl tl' → Step (.cons hd tl) (.cons hd tl')
  | head : Step v v' → Step (.head v) (.head v')
  | tail : Step v v' → Step (.tail v) (.tail v')
  | headCons : Value hd → Value tl → Step (.head (.cons hd tl)) hd
  | tailCons : Value hd → Value tl → Step (.tail (.cons hd tl)) tl

/-- Target: a step preserves the type. -/
def preservation : Prop :=
  ∀ (t t' : Tm) (T : Ty), HasType t T → Step t t' → HasType t' T

/-- Target: a well-typed term is a value or takes a step. -/
def progress : Prop :=
  ∀ (t : Tm) (T : Ty), HasType t T → Value t ∨ ∃ t', Step t t'

end Problems.Medium.DepVec
