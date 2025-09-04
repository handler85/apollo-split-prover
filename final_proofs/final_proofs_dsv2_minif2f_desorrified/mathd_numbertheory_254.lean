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
theorem mathd_numbertheory_254 : (239 + 174 + 83) % 10 = 6 := by
  have h_sum : 239 + 174 + 83 = 496 := by
    norm_num
    <;> rfl
  have h_mod : 496 % 10 = 6 := by
    norm_num
    <;> rfl
  have h_final : (239 + 174 + 83) % 10 = 6 := by
    rw [h_sum]
    <;> simp [h_mod]
    <;> norm_num
    <;> rfl
  exact h_final