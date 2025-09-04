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
theorem mathd_numbertheory_66 : 194 % 11 = 7 := by
  have h_main : 194 % 11 = 7 := by
    norm_num [Nat.mod_eq_of_lt, Nat.div_eq_of_lt]
    <;> rfl
    <;> norm_num
    <;> rfl
  apply h_main