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
theorem mathd_algebra_141 (a b : ℝ) (h₁ : a * b = 180) (h₂ : 2 * (a + b) = 54) :
    a ^ 2 + b ^ 2 = 369 := by
    have h_sum : a + b = 27 := by
        have h₃ : 2 * (a + b) = 54  := by
      
            gcongr
        have h₄ : a + b = 27 := by
            linarith
        exact h₄
    have h_sum_sq : a ^ 2 + b ^ 2 = 369 := by
        have h₃ : a ^ 2 + b ^ 2 = 369 := by
            have h₄ : a ^ 2 + b ^ 2 = (a + b) ^ 2 - 2 * (a * b) := by
                ring
            rw [h₄]
            have h₅ : a + b = 27  := by
        
                gcongr
            have h₆ : a * b = 180  := by
        
                gcongr
            rw [h₅, h₆]
            norm_num
            <;> nlinarith
        exact h₃
    exact h_sum_sq