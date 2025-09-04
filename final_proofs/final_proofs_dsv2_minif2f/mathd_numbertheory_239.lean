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
theorem mathd_numbertheory_239 : (∑ k in Finset.Icc 1 12, k) % 4 = 2 := by
  have h_sum : (∑ k in Finset.Icc 1 12, k) = 78 := by
    rfl
  have h_mod : (∑ k in Finset.Icc 1 12, k) % 4 = 2 := by
    rw [h_sum]
    <;> norm_num
    <;> rfl
  exact h_mod