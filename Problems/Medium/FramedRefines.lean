import Std

/-!
# Framed refinement

A small, self-contained model of the shape used by `lean-llvm`'s framed
refinement: a behaviour returns a value, a memory and an allocator state, and
two behaviours refine each other when they agree on the value and the
allocator and on every address outside a frame.

This is not a port of `LeanLLVM.Frames`; it is a statement of the same
relation at a size that fits one problem.  The targets are the algebraic
properties a caller relies on: reflexivity, transitivity, frame weakening, and
that a write inside the frame is admitted while a write outside it is not.
-/

namespace Problems.Medium.FramedRefines

/-- A behaviour's observable result. -/
structure Outcome where
  ret : Nat
  mem : Nat → Nat
  alloc : Nat

abbrev Beh := Nat → Outcome

/-- Update one memory cell. -/
def writeMem (m : Nat → Nat) (a v : Nat) : Nat → Nat :=
  fun x => if x = a then v else m x

/-- The memories agree at every address outside `frame`. -/
def AgreeOutside (frame : Nat → Prop) (m₁ m₂ : Nat → Nat) : Prop :=
  ∀ a, ¬ frame a → m₁ a = m₂ a

/-- `target` refines `source` inside `frame`: the value and allocator agree,
and memory may differ only inside the frame. -/
def RefinesWithin (frame : Nat → Prop) (target source : Beh) : Prop :=
  ∀ x,
    (target x).ret = (source x).ret
    ∧ (target x).alloc = (source x).alloc
    ∧ AgreeOutside frame (target x).mem (source x).mem

/-- Target: every behaviour refines itself in every frame. -/
def refines_refl : Prop := ∀ (frame : Nat → Prop) (b : Beh), RefinesWithin frame b b

/-- Target: refinement composes, with the union of the two frames. -/
def refines_trans : Prop :=
  ∀ (f g : Nat → Prop) (a b c : Beh),
    RefinesWithin g b c → RefinesWithin f a b → RefinesWithin (fun x => f x ∨ g x) a c

/-- Target: a smaller frame gives a stronger relation. -/
def frame_weaken : Prop :=
  ∀ (f g : Nat → Prop) (a b : Beh),
    (∀ x, g x → f x) → RefinesWithin f a b → RefinesWithin g a b

/-- Target: writing one cell inside the frame is a refinement of the same
behaviour with the old value at that cell. -/
def write_inside_frame : Prop :=
  ∀ (frame : Nat → Prop) (a : Nat) (v : Nat) (b : Beh),
    frame a →
    RefinesWithin frame
      (fun x => { b x with mem := writeMem (b x).mem a v })
      (fun x => { b x with mem := writeMem (b x).mem a ((b x).mem a) })

/-- Target: a write outside the frame is not a refinement in that frame. -/
def write_outside_frame_rejected : Prop :=
  ∃ (frame : Nat → Prop) (a : Nat) (v : Nat) (b : Beh),
    ¬ frame a ∧ v ≠ (b 0).mem a
    ∧ ¬ RefinesWithin frame
        (fun x => { b x with mem := writeMem (b x).mem a v })
        b

end Problems.Medium.FramedRefines
