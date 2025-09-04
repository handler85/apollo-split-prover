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
theorem mathd_algebra_208 : Real.sqrt 1000000 - 1000000 ^ ((1 : ℝ) / 3) = 900 := by
    have h_sqrt : Real.sqrt 1000000 = 1000 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;>
        linarith [Real.sqrt_nonneg 1000000]
    have h_cuberoot : (1000000 : ℝ) ^ ((1 : ℝ) / 3) = 100 := by
        have h₀ : (1000000 : ℝ) ^ ((1 : ℝ) / 3) = 100 := by
            have h₁ : (1000000 : ℝ) = 100 ^ 3  := by
                norm_num
            rw [h₁]
      
      
            norm_num <;>
            ring_nf <;>
            norm_num <;>
      
            norm_num <;>
            ring_nf <;>
            norm_num
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
            sorry
        rw [h₀]
        <;>
        norm_num
    have h_main : Real.sqrt 1000000 - 1000000 ^ ((1 : ℝ) / 3) = 900 := by
        rw [h_sqrt, h_cuberoot]
        <;> norm_num
        <;>
        linarith
    rw [h_main]
    <;> norm_num