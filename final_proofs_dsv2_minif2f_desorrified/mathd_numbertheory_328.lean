import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
set_option pp.instanceTypes true
set_option pp.numericTypes true
set_option pp.coercions.types true
set_option pp.letVarTypes true
set_option pp.structureInstanceTypes true
set_option pp.instanceTypes true
set_option pp.mvars.withType true
set_option pp.coercions true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
theorem mathd_numbertheory_328 : 5 ^ 999999 % 7 = 6 := by
  have h_main : 5 ^ 999999 % 7 = 6 := by
    rw [← Nat.mod_add_div (5 ^ 999999) 7]
    norm_num
    <;>
    rfl
    <;>
    simp [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
    <;>
    norm_num
    <;>
    rfl
  exact h_main