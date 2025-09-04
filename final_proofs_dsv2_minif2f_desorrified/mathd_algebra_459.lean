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
theorem mathd_algebra_459 (a b c d : ℚ) (h₀ : 3 * a = b + c + d) (h₁ : 4 * b = a + c + d)
    (h₂ : 2 * c = a + b + d) (h₃ : 8 * a + 10 * b + 6 * c = 24) : ↑d.den + d.num = 28 := by
    have h_b : b = 4 / 5 := by
        have h₄ : 5 * b = 4 * a := by
            linarith
        have h₅ : 3 * a = b + c + d  := by
            linarith
        have h₆ : 4 * b = a + c + d  := by
            linarith
        have h₇ : 2 * c = a + b + d  := by
            linarith
        have h₈ : 8 * a + 10 * b + 6 * c = 24  := by
            linarith
        ring_nf at *
        --nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 4 / 5), sq_nonneg (c - 4 / 3)
            --sq_nonneg (d - 13 / 15)]
        linarith
    have h_a : a = 1 := by
        have h₄ : 5 * b = 4 * a  := by
            linarith
        have h₅ : b = 4 / 5  := by
            linarith
        have h₆ : 5 * (4 / 5 : ℚ) = 4 * a := by
            rw [h₅] at h₄
            linarith
        have h₇ : a = 1 := by
            ring_nf at h₆ ⊢
            nlinarith
        exact h₇
    have h_c : c = 4 / 3 := by
        have h₄ : 3 * a = b + c + d  := by
            linarith
        have h₅ : 4 * b = a + c + d  := by
            linarith
        have h₆ : 2 * c = a + b + d  := by
            linarith
        have h₇ : 8 * a + 10 * b + 6 * c = 24  := by
            linarith
        have h₈ : b = 4 / 5  := by
            linarith
        have h₉ : a = 1  := by
            linarith
        field_simp [h₈, h₉] at h₄ h₅ h₆ h₇ ⊢
        <;> ring_nf at h₄ h₅ h₆ h₇ ⊢ <;> nlinarith
    have h_d : d = 13 / 15 := by
        have h₄ : 3 * a = b + c + d  := by
            linarith
        have h₅ : 4 * b = a + c + d  := by
            linarith
        have h₆ : 2 * c = a + b + d  := by
            linarith
        have h₇ : 8 * a + 10 * b + 6 * c = 24  := by
            linarith
        have h₈ : b = 4 / 5  := by
            linarith
        have h₉ : a = 1  := by
            linarith
        have h₁₀ : c = 4 / 3  := by
            linarith
        field_simp [h₈, h₉, h₁₀] at h₄ h₅ h₆ h₇ ⊢
        <;> ring_nf at h₄ h₅ h₆ h₇ ⊢ <;> nlinarith
    have h_main : ↑d.den + d.num = 28 := by
        have h₅ : d = 13 / 15  := by
            exact h_d
        rw [h₅]
        have h₆ : (13 / 15 : ℚ).num = 13  := by
            norm_num [Rat.num_div_den]
        have h₇ : (13 / 15 : ℚ).den = 15  := by
            norm_num [Rat.num_div_den]
    
        <;> norm_num
        <;> rfl
        linarith
    exact h_main