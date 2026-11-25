import Std

/-!
# Fuel-bounded Euclid

`gcdAux fuel a b` performs at most `fuel` Euclid steps.  The first target says
that with `fuel = a + b` it returns a greatest common divisor; the second says
the edge case `b = 0`.

Nothing here is proved.  The targets are `Prop`-valued definitions, so a proof
module states a theorem of exactly that type and the harness compares the two.
-/

namespace Problems.Easy.Gcd

/-- `d` is a greatest common divisor of `a` and `b`. -/
def IsGcd (d a b : Nat) : Prop :=
  d ∣ a ∧ d ∣ b ∧ ∀ e, e ∣ a → e ∣ b → e ∣ d

/-- Euclid, bounded by `fuel`.  A zero remainder ends the loop. -/
def gcdAux : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | _, a, 0 => a
  | fuel + 1, a, b + 1 => gcdAux fuel (b + 1) (a % (b + 1))

/-- The bounded Euclid with enough fuel for any pair. -/
def gcd (a b : Nat) : Nat := gcdAux (a + b) a b

/-- Target: for positive `b`, `gcd a b` is a greatest common divisor. -/
def gcd_isGcd : Prop := ∀ a b, 0 < b → IsGcd (gcd a b) a b

/-- Target: the zero case returns `a` unchanged. -/
def gcd_zero : Prop := ∀ a, gcd a 0 = a

end Problems.Easy.Gcd
