import Std

/-!
# A stack compiler for arithmetic expressions

Expressions are compiled left-to-right to stack instructions.  `run` executes a
program from a stack whose head is the top.  The target says compilation is
correct for every expression and every initial stack.
-/

namespace Problems.Easy.Stack

inductive Expr where
  | lit : Nat → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr

inductive Instr where
  | push : Nat → Instr
  | add : Instr
  | mul : Instr

def eval : Expr → Nat
  | .lit n => n
  | .add a b => eval a + eval b
  | .mul a b => eval a * eval b

def compile : Expr → List Instr
  | .lit n => [.push n]
  | .add a b => compile a ++ compile b ++ [.add]
  | .mul a b => compile a ++ compile b ++ [.mul]

/-- Execute instructions.  The head of the list is the top of the stack. -/
def run : List Nat → List Instr → Option (List Nat)
  | st, [] => some st
  | st, .push n :: is => run (n :: st) is
  | x :: y :: st, .add :: is => run ((y + x) :: st) is
  | x :: y :: st, .mul :: is => run ((y * x) :: st) is
  | _, _ :: _ => none

/-- Target: the compiled program leaves the value on top and the initial stack
under it. -/
def compile_correct : Prop := ∀ (e : Expr) (st : List Nat), run st (compile e) = some (eval e :: st)

end Problems.Easy.Stack
