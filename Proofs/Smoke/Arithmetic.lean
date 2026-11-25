import Problems.Smoke.Arithmetic

namespace Problems.Smoke.Arithmetic

theorem add_zero_proof : add_zero := by
  intro n
  exact Nat.add_zero n

theorem add_comm_proof : add_comm := by
  intro a b
  exact Nat.add_comm a b

theorem one_plus_one_proof : one_plus_one := by
  decide

end Problems.Smoke.Arithmetic
