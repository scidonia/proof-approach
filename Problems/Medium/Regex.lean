import Std

/-!
# Regular expression matching

Regular expressions over the alphabet `Nat`, their language as an inductive
predicate, and the textbook matcher.  The matcher threads a prefix through
`matchStar` so that the empty-match case is decided at the end of the input
rather than assumed up front; the targets relate the matcher to the language.

`matches` is a reserved word in Lean, so the matcher is written `«matches»`;
the declaration's name is `matches`, and the target below spells it `«matches»`.
-/

namespace Problems.Medium.Regex

/-- Regular expressions over `Nat`. -/
inductive Regex where
  | empty : Regex
  | eps : Regex
  | char : Nat → Regex
  | cat : Regex → Regex → Regex
  | alt : Regex → Regex → Regex
  | star : Regex → Regex

/-- The language of a regular expression.  `star` is the reflexive-transitive
closure of concatenation: no pieces, or one piece followed by more pieces. -/
inductive Lang : Regex → List Nat → Prop where
  | eps : Lang .eps []
  | char (n : Nat) : Lang (.char n) [n]
  | cat {r s : Regex} {x y : List Nat} :
      Lang r x → Lang s y → Lang (.cat r s) (x ++ y)
  | altl {r s : Regex} {x : List Nat} : Lang r x → Lang (.alt r s) x
  | altr {r s : Regex} {x : List Nat} : Lang s x → Lang (.alt r s) x
  | star_nil {r : Regex} : Lang (.star r) []
  | star_cons {r : Regex} {x y : List Nat} :
      Lang r x → Lang (.star r) y → Lang (.star r) (x ++ y)

mutual
  /-- Match a list against a regular expression.  `cat` tries every split point;
  `star` delegates to the accumulator `matchStar`. -/
  def «matches» : Regex → List Nat → Bool
    | .empty, _ => false
    | .eps, s => s.isEmpty
    | .char n, s => s == [n]
    | .cat r₁ r₂, s =>
        (List.range (s.length + 1)).any fun i =>
          «matches» r₁ (s.take i) && «matches» r₂ (s.drop i)
    | .alt r₁ r₂, s => «matches» r₁ s || «matches» r₂ s
    | .star r, s => matchStar r [] s
  termination_by r s => (sizeOf r, s.length)
  decreasing_by all_goals simp_wf <;> omega

  /-- Match a `star` body left to right.  `cur` is the segment accumulated so
  far and `rest` is what remains.  A nonempty `cur` may be closed whenever it
  matches `r`, and the next character starts a fresh segment; at the end `cur`
  itself must match unless it is empty, which is the empty match. -/
  def matchStar (r : Regex) : List Nat → List Nat → Bool
    | cur, [] => cur.isEmpty || «matches» r cur
    | cur, c :: cs =>
        (¬ cur.isEmpty && («matches» r cur && matchStar r [c] cs)) ||
          matchStar r (cur ++ [c]) cs
  termination_by cur rest => (sizeOf r, 2 * rest.length + cur.length + 1)
  decreasing_by all_goals simp_wf <;> omega
end

/-- Target: `matchStar` with an empty accumulator matches exactly the language
of `star r`.  This is the form the `star` case of `matches_iff` needs. -/
def matchStar_iff : Prop :=
  ∀ (r : Regex) (pre suf : List Nat),
    matchStar r pre suf = true ↔
      (pre = [] ∧ Lang (.star r) suf) ∨
        (∃ x y : List Nat, suf = x ++ y ∧ Lang r (pre ++ x) ∧ Lang (.star r) y)

/-- Target: the matcher decides the language of a regular expression. -/
def matches_iff : Prop :=
  ∀ (r : Regex) (s : List Nat), «matches» r s = true ↔ Lang r s

end Problems.Medium.Regex
