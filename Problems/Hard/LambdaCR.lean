import Std

/-!
# Church–Rosser via parallel reduction

Untyped lambda terms in de Bruijn form, single-step beta reduction, Martin-Löf
parallel reduction, and the targets of the Tait–Martin-Löf development: the
diamond property for parallel reduction, its relation to beta reduction, and
confluence of beta reduction.
-/

namespace Relation

/-- Reflexive transitive closure of a relation; core `Std` provides only
`TransGen`, so the standard closure is defined here. -/
inductive ReflTransGen {α : Sort u} (r : α → α → Prop) : α → α → Prop where
  | refl (a : α) : ReflTransGen r a a
  | tail {a b c : α} : ReflTransGen r a b → r b c → ReflTransGen r a c

end Relation

namespace Problems.Hard.LambdaCR

/-- Untyped lambda terms with de Bruijn indices. -/
inductive Tm where
  | var : Nat → Tm
  | lam : Tm → Tm
  | app : Tm → Tm → Tm
  deriving Repr, DecidableEq

/-- Shift free variables at or above the cutoff `d` up by one. -/
def shift (d : Nat) : Tm → Tm
  | .var n => if n < d then .var n else .var (n + 1)
  | .lam t => .lam (shift (d + 1) t)
  | .app a b => .app (shift d a) (shift d b)

/-- Substitute `s` for variable `j`, lowering the variables above it. -/
def subst (j : Nat) (s : Tm) : Tm → Tm
  | .var n => if n = j then s else if n > j then .var (n - 1) else .var n
  | .lam t => .lam (subst (j + 1) (shift 0 s) t)
  | .app a b => .app (subst j s a) (subst j s b)

/-- One step of beta reduction, with congruence under abstraction and
application. -/
inductive Beta : Tm → Tm → Prop where
  | beta (t s : Tm) : Beta (.app (.lam t) s) (subst 0 s t)
  | appL (a a' : Tm) (b : Tm) : Beta a a' → Beta (.app a b) (.app a' b)
  | appR (a : Tm) (b b' : Tm) : Beta b b' → Beta (.app a b) (.app a b')
  | lam (t t' : Tm) : Beta t t' → Beta (.lam t) (.lam t')

/-- Martin-Löf parallel reduction: beta with both the body and the argument
reduced in the same step. -/
inductive ParRed : Tm → Tm → Prop where
  | var (n : Nat) : ParRed (.var n) (.var n)
  | lam (t t' : Tm) : ParRed t t' → ParRed (.lam t) (.lam t')
  | app (a a' b b' : Tm) : ParRed a a' → ParRed b b' → ParRed (.app a b) (.app a' b')
  | beta (t t' s s' : Tm) :
      ParRed t t' → ParRed s s' → ParRed (.app (.lam t) s) (subst 0 s' t')

/-- Reflexive transitive closure of beta reduction. -/
def BetaStar : Tm → Tm → Prop := Relation.ReflTransGen Beta

/-- Target: parallel reduction has the diamond property. -/
def parred_diamond : Prop :=
  ∀ (t u v : Tm), ParRed t u → ParRed t v → ∃ w : Tm, ParRed u w ∧ ParRed v w

/-- Target: every parallel reduction is a beta reduction sequence. -/
def parred_betaStar : Prop := ∀ (t u : Tm), ParRed t u → BetaStar t u

/-- Target: a beta reduction sequence can be followed by one parallel reduction
to a common term. -/
def betaStar_parred : Prop :=
  ∀ (t u : Tm), BetaStar t u → ∃ v : Tm, ParRed t v ∧ BetaStar u v

/-- Target: beta reduction is confluent (Church–Rosser). -/
def church_rosser : Prop :=
  ∀ (t u v : Tm), BetaStar t u → BetaStar t v → ∃ w : Tm, BetaStar u w ∧ BetaStar v w

end Problems.Hard.LambdaCR
