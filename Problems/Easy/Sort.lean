import Std

/-!
# Insertion sort

`sort` is insertion sort on `Nat`.  The two targets are the two halves of its
specification: the output is sorted, and it is a permutation of the input.
-/

namespace Problems.Easy.Sort

/-- Insert `x` into an already sorted list. -/
def insert (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insert x ys

/-- Insertion sort. -/
def sort : List Nat → List Nat
  | [] => []
  | x :: xs => insert x (sort xs)

/-- Target: the output is sorted by `≤`. -/
def sort_sorted : Prop := ∀ l : List Nat, (sort l).Pairwise (· ≤ ·)

/-- Target: the output is a permutation of the input. -/
def sort_perm : Prop := ∀ l : List Nat, (sort l).Perm l

end Problems.Easy.Sort
