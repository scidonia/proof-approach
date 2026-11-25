import Std

/-!
# STLC with references and a store

Bespoke mid-tier problem in the shape of `rocq-piler`'s `pcf_ref` example:
a store typing `St`, a heap `s`, a typing judgement `HasType Γ St t T`, a
heap-typing predicate, and preservation stated with a store typing that
extends the old one.  The language is STLC plus references, without PCF's
arithmetic and fixpoint, so the proof is a metatheory exercise rather than a
research one.

The store is a list of closed values indexed by location.  `ref v` allocates at
`s.length`, appending to both the store and its typing; `assign` updates in
place; `deref` reads.  `StoreTyped` requires the store and its typing to have
the same length and every stored value to be typed at its location's type.
-/

namespace Problems.Medium.RefStore

inductive Ty where
  | unit : Ty
  | arr : Ty → Ty → Ty
  | ref : Ty → Ty

inductive Tm where
  | var : Nat → Tm
  | lam : Ty → Tm → Tm
  | app : Tm → Tm → Tm
  | unit : Tm
  | ref : Tm → Tm
  | deref : Tm → Tm
  | assign : Tm → Tm → Tm
  | loc : Nat → Tm

abbrev Ctx := List Ty
abbrev Store := List Tm
abbrev StoreTy := List Ty

/-- Extrinsic typing.  `St` is the store typing. -/
inductive HasType : Ctx → StoreTy → Tm → Ty → Prop where
  | var : Γ[n]? = some T → HasType Γ St (.var n) T
  | lam : HasType (A :: Γ) St t B → HasType Γ St (.lam A t) (.arr A B)
  | app : HasType Γ St f (.arr A B) → HasType Γ St a A →
      HasType Γ St (.app f a) B
  | unit : HasType Γ St .unit .unit
  | loc : St[n]? = some T → HasType Γ St (.loc n) (.ref T)
  | ref : HasType Γ St t T → HasType Γ St (.ref t) (.ref T)
  | deref : HasType Γ St t (.ref T) → HasType Γ St (.deref t) T
  | assign : HasType Γ St t₁ (.ref T) → HasType Γ St t₂ T →
      HasType Γ St (.assign t₁ t₂) .unit

/-- Canonical forms. -/
inductive Value : Tm → Prop where
  | unit : Value .unit
  | lam : Value (.lam A t)
  | loc : Value (.loc n)

/-- Shift free variables at or above `k` up by one. -/
def shift (k : Nat) : Tm → Tm
  | .var n => if n < k then .var n else .var (n + 1)
  | .lam A t => .lam A (shift (k + 1) t)
  | .app f a => .app (shift k f) (shift k a)
  | .unit => .unit
  | .ref t => .ref (shift k t)
  | .deref t => .deref (shift k t)
  | .assign t₁ t₂ => .assign (shift k t₁) (shift k t₂)
  | .loc n => .loc n

/-- Replace variable `j` and close up the indices above it. -/
def subst (j : Nat) (s : Tm) : Tm → Tm
  | .var n => if n < j then .var n else if n = j then s else .var (n - 1)
  | .lam A t => .lam A (subst (j + 1) (shift 0 s) t)
  | .app f a => .app (subst j s f) (subst j s a)
  | .unit => .unit
  | .ref t => .ref (subst j s t)
  | .deref t => .deref (subst j s t)
  | .assign t₁ t₂ => .assign (subst j s t₁) (subst j s t₂)
  | .loc n => .loc n

/-- Substitute a term for the innermost variable. -/
def subst0 (b a : Tm) : Tm := subst 0 a b

/-- The store and its typing have the same length, and every stored value is
typed at its location's type. -/
def StoreTyped (Γ : Ctx) (St : StoreTy) (s : Store) : Prop :=
  s.length = St.length ∧
    ∀ (n : Nat) (v : Tm) (T : Ty),
      s[n]? = some v → St[n]? = some T → HasType Γ St v T

/-- The new store typing extends the old one. -/
def StoreExtends (St St' : StoreTy) : Prop := ∃ Δ, St' = St ++ Δ

/-- Small-step reduction on a term and a store. -/
inductive Step : Tm → Store → Tm → Store → Prop where
  | app_lam : Value v → Step (.app (.lam A b) v) s (subst0 b v) s
  | app_fun : Step f s f' s' → Step (.app f a) s (.app f' a) s'
  | app_arg : Value f → Step a s a' s' → Step (.app f a) s (.app f a') s'
  | ref_val : Value v → Step (.ref v) s (.loc s.length) (s ++ [v])
  | ref_step : Step t s t' s' → Step (.ref t) s (.ref t') s'
  | deref_loc : s[n]? = some v → Step (.deref (.loc n)) s v s
  | deref_step : Step t s t' s' → Step (.deref t) s (.deref t') s'
  | assign_loc : Value v → s[n]? = some old →
      Step (.assign (.loc n) v) s .unit (s.set n v)
  | assign_fun : Step t₁ s t₁' s' → Step (.assign t₁ t₂) s (.assign t₁' t₂) s'
  | assign_arg : Value t₁ → Step t₂ s t₂' s' →
      Step (.assign t₁ t₂) s (.assign t₁ t₂') s'

/-- Target: the context-split substitution lemma. -/
def subst_preserves_typing : Prop :=
  ∀ (St : StoreTy) (Γ₁ : Ctx) (A : Ty) (t : Tm) (Γ₂ : Ctx) (u : Tm) (B : Ty),
    HasType Γ₁ St t A → HasType (Γ₁ ++ A :: Γ₂) St u B →
    HasType (Γ₁ ++ Γ₂) St (subst Γ₁.length t u) B

/-- Target: typing is stable under extending the store typing. -/
def store_typing_weaken : Prop :=
  ∀ (Γ : Ctx) (St Δ : StoreTy) (t : Tm) (T : Ty),
    HasType Γ St t T → HasType Γ (St ++ Δ) t T

/-- Target: a step preserves typing, with a store typing that extends the old
one and still types the new store. -/
def preservation : Prop :=
  ∀ (Γ : Ctx) (St : StoreTy) (t : Tm) (T : Ty) (s : Store)
    (t' : Tm) (s' : Store),
    HasType Γ St t T → StoreTyped Γ St s → Step t s t' s' →
    ∃ St', StoreExtends St St' ∧ StoreTyped Γ St' s' ∧ HasType Γ St' t' T

/-- Target: a closed well-typed term is a value or takes a step. -/
def progress : Prop :=
  ∀ (St : StoreTy) (t : Tm) (T : Ty) (s : Store),
    HasType [] St t T → StoreTyped [] St s →
    Value t ∨ ∃ t' s', Step t s t' s'

end Problems.Medium.RefStore
