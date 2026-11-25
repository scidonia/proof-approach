import Std

/-!
# Merge sort correctness

Adapted from the `mergesort` challenge in `rocq-piler`'s incomplete benchmark
corpus.  The definitions are the textbook ones: merge two sorted lists, split a
list into alternating halves, and merge-sort with a fuel bound equal to the
input length.

The top targets are that the result is sorted and a permutation of the input.
The four helper targets are the pieces a proof needs, exposed separately so a
partial proof is scored.
-/

namespace Problems.Medium.MergeSort

/-- Merge two lists, assuming both are sorted. -/
def merge : List Nat → List Nat → List Nat
  | [], l2 => l2
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys =>
      if x ≤ y then x :: merge xs (y :: ys)
      else y :: merge (x :: xs) ys

/-- Split a list into alternating halves. -/
def split : List Nat → List Nat × List Nat
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: rest =>
      let (l1, l2) := split rest
      (x :: l1, y :: l2)

/-- Merge sort, fuel-bounded.  The top targets instantiate `fuel = l.length`. -/
def mergesort : Nat → List Nat → List Nat
  | 0, l => l
  | _ + 1, [] => []
  | _ + 1, [x] => [x]
  | fuel + 1, x :: y :: rest =>
      let (l1, l2) := split (x :: y :: rest)
      merge (mergesort fuel l1) (mergesort fuel l2)

/-- Target: merging two sorted lists is sorted. -/
def merge_sorted : Prop :=
  ∀ {l₁ l₂ : List Nat},
    l₁.Pairwise (· ≤ ·) → l₂.Pairwise (· ≤ ·) → (merge l₁ l₂).Pairwise (· ≤ ·)

/-- Target: merging is a permutation of the concatenation. -/
def merge_perm : Prop :=
  ∀ (l₁ l₂ : List Nat), (merge l₁ l₂).Perm (l₁ ++ l₂)

/-- Target: the two halves of a split are a permutation of the input. -/
def split_perm : Prop :=
  ∀ l : List Nat, ((split l).1 ++ (split l).2).Perm l

/-- Target: the two halves of a split have the input's length. -/
def split_length : Prop :=
  ∀ l : List Nat, (split l).1.length + (split l).2.length = l.length

/-- Target: merge sort returns a sorted list. -/
def mergesort_sorted : Prop :=
  ∀ l : List Nat, (mergesort l.length l).Pairwise (· ≤ ·)

/-- Target: merge sort returns a permutation of the input. -/
def mergesort_perm : Prop :=
  ∀ l : List Nat, (mergesort l.length l).Perm l

end Problems.Medium.MergeSort
