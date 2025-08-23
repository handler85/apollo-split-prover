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
lemma aime_1997_p9_2
    (a : ℝ)
    (h₀ : (0 : ℝ) < a)
    (h₂ : (2 : ℝ) < a ^ (2 : ℕ))
    (h₃ : a ^ (2 : ℕ) < (3 : ℝ))
    (h_floor_a2 : ⌊a ^ (2 : ℕ)⌋ = (2 : ℤ))
    (h_floor_inv_a : (0 : ℝ) ≤ a ∧ a⁻¹ < (1 : ℝ))
    (h₁ : Int.fract a⁻¹ = (-2 : ℝ) + a ^ (2 : ℕ)) :
    a⁻¹ = (-2 : ℝ) + a ^ (2 : ℕ) := by
    have h_main : a⁻¹ = (-2 : ℝ) + a ^ (2 : ℕ) := by
        have h₄ : a > 1 := by
            by_contra h
            have h₅ : a ≤ 1  := by
                linarith
            have h₆ : a ^ 2 ≤ a := by
                nlinarith
            nlinarith
        have h₅ : a⁻¹ > 0  := by
            positivity
        have h₆ : a⁻¹ < 1 := by
            have h₇ : a > 1  := by
        
                gcongr
            have h₈ : a⁻¹ < 1 := by
                rw [inv_lt_one_iff_of_pos h₀]
                nlinarith
            exact h₈
        have h₇ : Int.fract a⁻¹ = a⁻¹ - ⌊a⁻¹⌋ := by
            rw [Int.fract]
            <;> simp [Int.floor_eq_iff]
            <;> norm_num
            <;> linarith
        rw [h₇] at h₁
        have h₈ : ⌊a⁻¹⌋ = 0 := by
            have h₉ : 0 ≤ a⁻¹  := by
                positivity
            have h₁₀ : a⁻¹ < 1  := by
        
                gcongr
            have h₁₁ : ⌊a⁻¹⌋ = 0 := by
                rw [Int.floor_eq_iff]
                norm_num at h₉ h₁₀ ⊢
                constructor <;> norm_num <;>
                (try norm_num at * <;> nlinarith) <;>
                (try constructor <;> linarith) <;>
                (try nlinarith) <;>
                (try linarith) <;>
                (try nlinarith)
                <;>
                (try linarith)
                <;>
                (try nlinarith)
            exact h₁₁
        rw [h₈] at h₁
        norm_num at h₁ ⊢
    
        gcongr
    exact h_main