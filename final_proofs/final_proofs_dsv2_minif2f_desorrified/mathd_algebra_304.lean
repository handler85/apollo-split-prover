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
theorem mathd_algebra_304 : 91 ^ 2 = 8281 := by
  have h_main : 91 ^ 2 = 8281 := by
    norm_num [pow_two]
    <;> rfl
    <;> simp_all
    <;> norm_num
    <;> rfl
  apply h_main