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
theorem amc12b_2020_p13 :
    Real.sqrt (Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3) =
        Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3) := by
    have h_main : Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3 = (Real.log 3 / Real.log 2) + (Real.log 2 / Real.log 3) + 2 := by
        have h₁ : Real.log 6 = Real.log 2 + Real.log 3 := by
            have h₂ : Real.log 6 = Real.log (2 * 3)  := by
                norm_num
            rw [h₂]
            have h₃ : Real.log (2 * 3) = Real.log 2 + Real.log 3 := by
                rw [Real.log_mul (by norm_num) (by norm_num)]
            rw [h₃]
        rw [h₁]
        have h₂ : (Real.log 2 + Real.log 3) / Real.log 2 + (Real.log 2 + Real.log 3) / Real.log 3 = (Real.log 3 / Real.log 2) + (Real.log 2 / Real.log 3) + 2 := by
            have h₃ : Real.log 2 > 0  := by
        
                try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
                sorry
            have h₄ : Real.log 3 > 0  := by
        
                try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
                sorry
            field_simp [h₃.ne', h₄.ne']
            <;> ring_nf
            <;> field_simp [h₃.ne', h₄.ne']
            <;> nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2), Real.log_pos (by norm_num : (1 : ℝ) < 3)]
        linarith
    have h_final : Real.sqrt (Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3) = Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3) := by
        rw [h_main]
        have h₁ : Real.sqrt ((Real.log 3 / Real.log 2) + (Real.log 2 / Real.log 3) + 2) = Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3) := by
            have h₂ : 0 < Real.log 2  := by
        
                try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
                sorry
            have h₃ : 0 < Real.log 3  := by
        
                exact Real.sqrt_nonneg (Real.log (3 : ℝ) / Real.log (2 : ℝ))
            have h₄ : 0 < Real.log 2 * Real.log 3  := by
                positivity
            have h₅ : 0 < Real.log 3 / Real.log 2  := by
                positivity
            have h₆ : 0 < Real.log 2 / Real.log 3  := by
                positivity
            have h₇ : 0 < Real.log 3 / Real.log 2 * (Real.log 2 / Real.log 3)  := by
                positivity
            have h₈ : Real.log 3 / Real.log 2 * (Real.log 2 / Real.log 3) = 1 := by
                field_simp
                <;> ring_nf
                <;> field_simp [h₂.ne', h₃.ne']
                <;> nlinarith
            have h₉ : (Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3)) ^ 2 = (Real.log 3 / Real.log 2) + (Real.log 2 / Real.log 3) + 2 := by
                --nlinarith [Real.sq_sqrt (show 0 ≤ Real.log 3 / Real.log 2 by positivity)
                    --Real.sq_sqrt (show 0 ≤ Real.log 2 / Real.log 3 by positivity)
                    --sq_nonneg (Real.sqrt (Real.log 3 / Real.log 2) - Real.sqrt (Real.log 2 / Real.log 3))]
                exact Real.sqrt_nonneg (Real.log (2 : ℝ) / Real.log (3 : ℝ))
            have h₁₀ : Real.sqrt ((Real.log 3 / Real.log 2) + (Real.log 2 / Real.log 3) + 2) = Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3) := by
                have h₁₁ : 0 ≤ Real.sqrt (Real.log 3 / Real.log 2)  := by
          
                    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
                have h₁₂ : 0 ≤ Real.sqrt (Real.log 2 / Real.log 3)  := by
          
                    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
                have h₁₃ : 0 ≤ Real.sqrt (Real.log 3 / Real.log 2) * Real.sqrt (Real.log 2 / Real.log 3)  := by
                    positivity
                have h₁₄ : (Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3)) ^ 2 = (Real.log 3 / Real.log 2) + (Real.log 2 / Real.log 3) + 2 := by
                    nlinarith
                have h₁₅ : Real.sqrt ((Real.log 3 / Real.log 2) + (Real.log 2 / Real.log 3) + 2) = Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3) := by
                    --rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_nonneg (Real.log 3 / Real.log 2), Real.sqrt_nonneg (Real.log 2 / Real.log 3)
                        --Real.sq_sqrt (show 0 ≤ Real.log 3 / Real.log 2 by positivity)
                        --Real.sq_sqrt (show 0 ≤ Real.log 2 / Real.log 3 by positivity)]
                    try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
                    sorry
                exact h₁₅
            exact h₁₀
        rw [h₁]
        <;>
        norm_num
        <;>
        linarith
    rw [h_final]
    <;>
    norm_num
    <;>
    linarith