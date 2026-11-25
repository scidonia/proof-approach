import Std

/-!
# Harness smoke problem

This exists to validate the run scaffolding, the statement hash, the type
check and the axiom check.  It is not part of the measured corpus.
-/

namespace Problems.Smoke.Arithmetic

def add_zero : Prop := ∀ n : Nat, n + 0 = n

def add_comm : Prop := ∀ a b : Nat, a + b = b + a

/-- A decidable target, so the harness's `native_decide` rejection can be
exercised. -/
abbrev one_plus_one : Prop := 1 + 1 = 2

end Problems.Smoke.Arithmetic
