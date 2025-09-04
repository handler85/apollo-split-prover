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
theorem amc12b_2021_p9 :
    Real.log 80 / Real.log 2 / (Real.log 2 / Real.log 40) -
        Real.log 160 / Real.log 2 / (Real.log 2 / Real.log 20) =
        2 := by
    have h₁ : Real.log 40 = Real.log (2^3 * 5) := by
        norm_num
        <;>
        rfl
    have h₂ : Real.log 20 = Real.log (2^2 * 5) := by
        norm_num
        <;>
        rfl
    have h₃ : Real.log 80 = Real.log (2^4 * 5) := by
        norm_num
        <;>
        rfl
    have h₄ : Real.log 160 = Real.log (2^5 * 5) := by
        norm_num
        <;>
        rfl
    have h_main : Real.log 80 / Real.log 2 / (Real.log 2 / Real.log 40) - Real.log 160 / Real.log 2 / (Real.log 2 / Real.log 20) = 2 := by
        have h₅ : Real.log 40 = Real.log (2 ^ 3 * 5)  := by
            rw [h₁]
        have h₆ : Real.log 20 = Real.log (2 ^ 2 * 5)  := by
            rw [h₂]
        have h₇ : Real.log 80 = Real.log (2 ^ 4 * 5)  := by
            rw [h₃]
        have h₈ : Real.log 160 = Real.log (2 ^ 5 * 5)  := by
            rw [h₄]
        have h₉ : Real.log 40 = 3 * Real.log 2 + Real.log 5 := by
            rw [h₅]
            have h₉₁ : Real.log (2 ^ 3 * 5) = Real.log (2 ^ 3) + Real.log 5 := by
                rw [Real.log_mul (by positivity) (by positivity)]
                <;> ring
            rw [h₉₁]
            have h₉₂ : Real.log (2 ^ 3) = 3 * Real.log 2 := by
                rw [Real.log_pow] <;> ring
                <;> norm_num
            rw [h₉₂]
            <;> ring
        have h₁₀ : Real.log 20 = 2 * Real.log 2 + Real.log 5 := by
            rw [h₆]
            have h₁₀₁ : Real.log (2 ^ 2 * 5) = Real.log (2 ^ 2) + Real.log 5 := by
                rw [Real.log_mul (by positivity) (by positivity)]
                <;> ring
            rw [h₁₀₁]
            have h₁₀₂ : Real.log (2 ^ 2) = 2 * Real.log 2 := by
                rw [Real.log_pow] <;> ring
                <;> norm_num
            rw [h₁₀₂]
            <;> ring
        have h₁₁ : Real.log 80 = 4 * Real.log 2 + Real.log 5 := by
            rw [h₇]
            have h₁₁₁ : Real.log (2 ^ 4 * 5) = Real.log (2 ^ 4) + Real.log 5 := by
                rw [Real.log_mul (by positivity) (by positivity)]
                <;> ring
            rw [h₁₁₁]
            have h₁₁₂ : Real.log (2 ^ 4) = 4 * Real.log 2 := by
                rw [Real.log_pow] <;> ring
                <;> norm_num
            rw [h₁₁₂]
            <;> ring
        have h₁₂ : Real.log 160 = 5 * Real.log 2 + Real.log 5 := by
            rw [h₈]
            have h₁₂₁ : Real.log (2 ^ 5 * 5) = Real.log (2 ^ 5) + Real.log 5 := by
                rw [Real.log_mul (by positivity) (by positivity)]
                <;> ring
            rw [h₁₂₁]
            have h₁₂₂ : Real.log (2 ^ 5) = 5 * Real.log 2 := by
                rw [Real.log_pow] <;> ring
                <;> norm_num
            rw [h₁₂₂]
            <;> ring
        have h₁₃ : Real.log 2 > 0  := by
      
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
            sorry
        have h₁₄ : Real.log 5 > 0  := by
      
            try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
            sorry
        have h₁₅ : Real.log 40 > 0 := by
            apply Real.log_pos
            norm_num
        have h₁₆ : Real.log 20 > 0 := by
            apply Real.log_pos
            norm_num
        field_simp [h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆]
        <;> ring_nf
        <;> field_simp [h₁₃, h₁₄]
        <;> nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2), Real.log_pos (by norm_num : (1 : ℝ) < 5)]
    exact h_main