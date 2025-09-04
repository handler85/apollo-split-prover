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
theorem mathd_algebra_398 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : 9 * b = 20 * c)
    (h₂ : 7 * a = 4 * b) : 63 * a = 80 * c := by
    have h_b_in_terms_of_a : b = (7 / 4 : ℝ) * a := by
        have h₃ : b = (7 / 4 : ℝ) * a := by
            have h₄ : 7 * a = 4 * b  := by
        
                gcongr
            have h₅ : b = (7 / 4 : ℝ) * a := by
                linarith
            exact h₅
        exact h₃
    have h_main : 63 * a = 80 * c := by
        have h₃ : 9 * b = 20 * c  := by
      
            gcongr
        have h₄ : b = (7 / 4 : ℝ) * a  := by
      
            gcongr
        have h₅ : 9 * ((7 / 4 : ℝ) * a) = 20 * c := by
            rw [h₄] at h₃
            exact h₃
        have h₆ : 63 * a = 80 * c := by
            ring_nf at h₅ ⊢
            nlinarith
        exact h₆
    exact h_main