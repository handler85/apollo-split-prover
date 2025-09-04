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
theorem amc12a_2021_p9 : (∏ k in Finset.range 7, (2 ^ 2 ^ k + 3 ^ 2 ^ k)) = 3 ^ 128 - 2 ^ 128 := by
  have h_main : (∏ k in Finset.range 7, (2 ^ 2 ^ k + 3 ^ 2 ^ k)) = 3 ^ 128 - 2 ^ 128 := by
    norm_num [Finset.prod_range_succ, pow_add, pow_mul, pow_one, pow_two, pow_three]
    <;>
    (try decide) <;>
    (try ring_nf) <;>
    (try norm_num) <;>
    (try
      {
        rfl
      }) <;>
    (try
      {
        simp_all [Finset.prod_range_succ, pow_add, pow_mul, pow_one, pow_two, pow_three]
        <;>
        norm_num
        <;>
        ring_nf
        <;>
        norm_num
        <;>
        rfl
      })
    <;>
    (try
      {
        simp_all [Finset.prod_range_succ, pow_add, pow_mul, pow_one, pow_two, pow_three]
        <;>
        norm_num
        <;>
        ring_nf
        <;>
        norm_num
        <;>
        rfl
      })
    <;>
    (try
      {
        simp_all [Finset.prod_range_succ, pow_add, pow_mul, pow_one, pow_two, pow_three]
        <;>
        norm_num
        <;>
        ring_nf
        <;>
        norm_num
        <;>
        rfl
      })
  exact h_main