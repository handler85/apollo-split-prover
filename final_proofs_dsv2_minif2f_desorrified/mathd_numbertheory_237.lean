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
theorem mathd_numbertheory_237 : (∑ k in Finset.range 101, k) % 6 = 4 := by
  have h_sum : (∑ k in Finset.range 101, k) = 5050 := by
    rfl
  have h_mod : 5050 % 6 = 4 := by
    norm_num
    <;> rfl
  have h_final : (∑ k in Finset.range 101, k) % 6 = 4 := by
    rw [h_sum]
    <;> simp [h_mod]
    <;> norm_num
    <;> rfl
  exact h_final