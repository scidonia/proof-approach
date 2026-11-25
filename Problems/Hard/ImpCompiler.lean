import Std

/-!
# A compiler from a small imperative language to a stack machine

Programs are compiled to absolute-address stack instructions: the machine has a
value stack, a program counter and a mutable state mapping variable names to
numbers.  Variables are loaded and stored by name, so the machine carries the
state explicitly; `run` returns the final state, stack and program counter.

Nothing here is proved.  Every target is a `Prop`-valued definition.
-/

namespace Problems.Hard.ImpCompiler

/-- Arithmetic expressions. -/
inductive AExp where
  | num : Nat → AExp
  | var : String → AExp
  | add : AExp → AExp → AExp
  | mul : AExp → AExp → AExp

/-- Boolean expressions. -/
inductive BExp where
  | tr : BExp
  | fls : BExp
  | not : BExp → BExp
  | and : BExp → BExp → BExp
  | lt : AExp → AExp → BExp

/-- Commands. -/
inductive Cmd where
  | skip : Cmd
  | assign : String → AExp → Cmd
  | seq : Cmd → Cmd → Cmd
  | ite : BExp → Cmd → Cmd → Cmd
  | while : BExp → Cmd → Cmd

/-- A state assigns a number to each variable name. -/
abbrev State := String → Nat

/-- The state that agrees with `s` except that `x` maps to `v`. -/
def setVar (s : State) (x : String) (v : Nat) : State :=
  fun y => if y = x then v else s y

/-- Evaluation of arithmetic expressions. -/
def aeval (s : State) : AExp → Nat
  | .num n => n
  | .var x => s x
  | .add a b => aeval s a + aeval s b
  | .mul a b => aeval s a * aeval s b

/-- Evaluation of boolean expressions. -/
def beval (s : State) : BExp → Bool
  | .tr => true
  | .fls => false
  | .not b => !beval s b
  | .and a b => beval s a && beval s b
  | .lt a b => decide (aeval s a < aeval s b)

/-- Big-step execution relation for terminating runs. -/
inductive Exec : Cmd → State → State → Prop where
  | skip (s) : Exec .skip s s
  | assign (s x a) : Exec (.assign x a) s (setVar s x (aeval s a))
  | seq {c₁ c₂ s s₁ s₂} :
      Exec c₁ s s₁ → Exec c₂ s₁ s₂ → Exec (.seq c₁ c₂) s s₂
  | iteTrue {b c₁ c₂ s s'} :
      beval s b = true → Exec c₁ s s' → Exec (.ite b c₁ c₂) s s'
  | iteFalse {b c₁ c₂ s s'} :
      beval s b = false → Exec c₂ s s' → Exec (.ite b c₁ c₂) s s'
  | whileFalse {b c s} : beval s b = false → Exec (.while b c) s s
  | whileTrue {b c s s₁ s₂} :
      beval s b = true → Exec c s s₁ → Exec (.while b c) s₁ s₂ →
        Exec (.while b c) s s₂

open Classical in
/-- Big-step execution: the final state if the command terminates. -/
noncomputable def exec (c : Cmd) (s : State) : Option State :=
  if h : ∃ s', Exec c s s' then some (Classical.choose h) else none

/-- Stack machine instructions.  Arithmetic and comparison instructions pop
their operands, with the top of the stack as the last operand.  Jumps are
absolute. -/
inductive Instr where
  | push : Nat → Instr
  | load : String → Instr
  | store : String → Instr
  | add : Instr
  | mul : Instr
  | lt : Instr
  | eqz : Instr
  | jmp : Nat → Instr
  | jz : Nat → Instr

/-- Execute one instruction, returning the next configuration. -/
def execInstr (s : State) (st : List Nat) : Instr → Nat → Option (State × List Nat × Nat)
  | .push n, pc => some (s, n :: st, pc + 1)
  | .load x, pc => some (s, s x :: st, pc + 1)
  | .store x, pc =>
      match st with
      | v :: rest => some (setVar s x v, rest, pc + 1)
      | [] => none
  | .add, pc =>
      match st with
      | x :: y :: rest => some (s, (y + x) :: rest, pc + 1)
      | _ => none
  | .mul, pc =>
      match st with
      | x :: y :: rest => some (s, (y * x) :: rest, pc + 1)
      | _ => none
  | .lt, pc =>
      match st with
      | x :: y :: rest => some (s, (if y < x then 1 else 0) :: rest, pc + 1)
      | _ => none
  | .eqz, pc =>
      match st with
      | v :: rest => some (s, (if v = 0 then 1 else 0) :: rest, pc + 1)
      | [] => none
  | .jmp a, _ => some (s, st, a)
  | .jz a, pc =>
      match st with
      | 0 :: rest => some (s, rest, a)
      | _ :: rest => some (s, rest, pc + 1)
      | [] => none

/-- Run for at most `fuel` instructions.  Reaching the end of the program halts
and returns the current program counter, which then equals the code length. -/
def go : Nat → State → List Nat → List Instr → Nat → Option (State × List Nat × Nat)
  | 0, _, _, _, _ => none
  | fuel + 1, s, st, prog, pc =>
      match prog[pc]? with
      | none => some (s, st, pc)
      | some i =>
          match execInstr s st i pc with
          | none => none
          | some (s', st', pc') => go fuel s' st' prog pc'

/-- Run a program from address `0` with the given fuel, state and stack. -/
def run (fuel : Nat) (s : State) (st : List Nat) (prog : List Instr) :
    Option (State × List Nat × Nat) :=
  go fuel s st prog 0

/-- Compilation of arithmetic expressions: the value is left on top. -/
def compileA : AExp → List Instr
  | .num n => [.push n]
  | .var x => [.load x]
  | .add a b => compileA a ++ compileA b ++ [.add]
  | .mul a b => compileA a ++ compileA b ++ [.mul]

/-- Compilation of boolean expressions: the truth value, as `1` or `0`, is left
on top. -/
def compileB : BExp → List Instr
  | .tr => [.push 1]
  | .fls => [.push 0]
  | .not b => compileB b ++ [.eqz]
  | .and a b => compileB a ++ compileB b ++ [.mul]
  | .lt a b => compileA a ++ compileA b ++ [.lt]

/-- Compile a command whose code starts at absolute address `base`.  The code is
stack neutral: it leaves the stack as it found it. -/
def compileFrom (base : Nat) : Cmd → List Instr
  | .skip => []
  | .assign x a => compileA a ++ [.store x]
  | .seq c₁ c₂ =>
      let l₁ := compileFrom base c₁
      l₁ ++ compileFrom (base + l₁.length) c₂
  | .ite b c₁ c₂ =>
      let cb := compileB b
      let l₁ := compileFrom (base + cb.length + 1) c₁
      let elsePc := base + cb.length + 1 + l₁.length + 1
      let l₂ := compileFrom elsePc c₂
      let endPc := elsePc + l₂.length
      cb ++ [.jz elsePc] ++ l₁ ++ [.jmp endPc] ++ l₂
  | .while b c =>
      let cb := compileB b
      let body := compileFrom (base + cb.length + 1) c
      let endPc := base + cb.length + 1 + body.length + 1
      cb ++ [.jz endPc] ++ body ++ [.jmp base]

/-- The compiled code of a command, laid out from address `0`. -/
def compile (c : Cmd) : List Instr := compileFrom 0 c

/-- Target: `exec` is deterministic. -/
def exec_deterministic : Prop :=
  ∀ (c : Cmd) (s s₁ s₂ : State),
    exec c s = some s₁ → exec c s = some s₂ → s₁ = s₂

/-- Target: a terminating command compiles to a program that, run with enough
fuel, halts with the same state on an empty stack. -/
def compile_correct : Prop :=
  ∀ (c : Cmd) (s s' : State), exec c s = some s' →
    ∃ fuel : Nat, run fuel s [] (compile c) = some (s', [], (compile c).length)

end Problems.Hard.ImpCompiler
