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
theorem mathd_algebra_296 : abs ((3491 - 60) * (3491 + 60) - 3491 ^ 2 : ℤ) = 3600 := by
  have h_main : abs ((3491 - 60) * (3491 + 60) - 3491 ^ 2 : ℤ) = 3600 := by
    norm_num [abs_eq, Int.mul_emod, Int.sub_emod, Int.add_emod, pow_two]
    <;>
    (try decide) <;>
    (try ring_nf) <;>
    (try norm_num) <;>
    (try omega) <;>
    (try
      {
        norm_num
        <;>
        rfl
      })
    <;>
    (try
      {
        simp [abs_eq_max_neg]
        <;>
        norm_num
        <;>
        rfl
      })
    <;>
    (try
      {
        norm_num
        <;>
        rfl
      })
  exact h_main