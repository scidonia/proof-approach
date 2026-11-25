import Std

/-!
# AVL trees

An AVL tree of `Nat` keys with insertion.  `bst` is the usual ordering
invariant, `balanced` bounds the difference between child heights by one, and
`insert` rebalances with single and double rotations on the way back up.
-/

namespace Problems.Medium.Avl

/-- Binary search trees with `Nat` keys at the nodes. -/
inductive Tree where
  | leaf : Tree
  | node : Tree → Nat → Tree → Tree
  deriving Repr, DecidableEq

/-- The height of a tree, with leaves at height `0`. -/
def height : Tree → Nat
  | .leaf => 0
  | .node l _ r => 1 + max (height l) (height r)

/-- Every key of the tree is smaller than `x`. -/
def allLt (x : Nat) : Tree → Prop
  | .leaf => True
  | .node l k r => k < x ∧ allLt x l ∧ allLt x r

/-- Every key of the tree is greater than `x`. -/
def allGt (x : Nat) : Tree → Prop
  | .leaf => True
  | .node l k r => x < k ∧ allGt x l ∧ allGt x r

/-- The binary search tree invariant: left keys are smaller and right keys are
greater, recursively. -/
def bst : Tree → Prop
  | .leaf => True
  | .node l k r => bst l ∧ bst r ∧ allLt k l ∧ allGt k r

/-- The AVL balance invariant: child heights differ by at most one, recursively. -/
def balanced : Tree → Prop
  | .leaf => True
  | .node l _ r =>
      balanced l ∧ balanced r ∧ height l ≤ height r + 1 ∧ height r ≤ height l + 1

/-- A right rotation at a left-heavy node. -/
def rotR : Tree → Tree
  | .node (.node a k b) m c => .node a k (.node b m c)
  | t => t

/-- A left rotation at a right-heavy node. -/
def rotL : Tree → Tree
  | .node a k (.node b m c) => .node (.node a k b) m c
  | t => t

/-- A left-right double rotation for the left-heavy, left-right-heavy case. -/
def rotLR : Tree → Tree
  | .node (.node a k (.node b m c)) z d => .node (.node a k b) m (.node c z d)
  | t => t

/-- A right-left double rotation for the right-heavy, right-left-heavy case. -/
def rotRL : Tree → Tree
  | .node a k (.node (.node b m c) z d) => .node (.node a k b) m (.node c z d)
  | t => t

/-- Restore balance at a node whose children are already balanced. -/
def balance : Tree → Tree
  | .leaf => .leaf
  | .node l k r =>
      if height l > height r + 1 then
        match l with
        | .leaf => .node l k r
        | .node ll _ lr =>
            if height lr ≤ height ll then rotR (.node l k r)
            else rotLR (.node l k r)
      else if height r > height l + 1 then
        match r with
        | .leaf => .node l k r
        | .node rl _ rr =>
            if height rl ≤ height rr then rotL (.node l k r)
            else rotRL (.node l k r)
      else
        .node l k r

/-- Insert a key into the tree, rebalancing on the way back up. -/
def insert (x : Nat) : Tree → Tree
  | .leaf => .node .leaf x .leaf
  | .node l k r =>
      if x < k then balance (.node (insert x l) k r)
      else if k < x then balance (.node l k (insert x r))
      else .node l k r

/-- Membership of a key in the tree. -/
def mem (x : Nat) : Tree → Prop
  | .leaf => False
  | .node l k r => x = k ∨ mem x l ∨ mem x r

/-- Target: insertion into a binary search tree yields a binary search tree. -/
def insert_bst : Prop := ∀ (x : Nat) (t : Tree), bst t → bst (insert x t)

/-- Target: insertion into a balanced AVL tree yields a balanced AVL tree. -/
def insert_balanced : Prop := ∀ (x : Nat) (t : Tree), balanced t → balanced (insert x t)

/-- Target: the inserted key is present in the resulting tree. -/
def insert_mem : Prop := ∀ (x : Nat) (t : Tree), mem x (insert x t)

end Problems.Medium.Avl
