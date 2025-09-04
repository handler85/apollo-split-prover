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
theorem mathd_algebra_441 (x : ℝ) (h₀ : x ≠ 0) :
    12 / (x * x) * (x ^ 4 / (14 * x)) * (35 / (3 * x)) = 10 := by
    have h_main : 12 / (x * x) * (x ^ 4 / (14 * x)) * (35 / (3 * x)) = 10 := by
        have h₁ : 12 / (x * x) * (x ^ 4 / (14 * x)) * (35 / (3 * x)) = 10 := by
            have h₂ : x ≠ 0  := by
        
                exact h₀
            field_simp [h₂, pow_succ, mul_assoc, mul_comm, mul_left_comm]
            <;> ring_nf
            <;> field_simp [h₂]
            <;> ring
            <;> norm_num
            <;>
            (try
                {
                    simp_all [mul_assoc]
                    <;> ring_nf
                    <;> field_simp [h₂]
                    <;> ring
                    <;> norm_num
                })
            <;>
            (try
                {
                    nlinarith [sq_pos_of_ne_zero h₂]
                })
        exact h₁
    exact h_main