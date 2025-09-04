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
theorem mathd_algebra_263 (y : ℝ) (h₀ : 0 ≤ 19 + 3 * y) (h₁ : Real.sqrt (19 + 3 * y) = 7) :
    y = 10 := by
    have h₂ : 19 + 3 * y = 49 := by
        have h₂₁ : Real.sqrt (19 + 3 * y) = 7  := by
      
            gcongr
        have h₂₂ : 0 ≤ 19 + 3 * y  := by
      
            gcongr
        have h₂₃ : Real.sqrt (19 + 3 * y) ^ 2 = 7 ^ 2  := by
            rw [h₂₁]
        have h₂₄ : Real.sqrt (19 + 3 * y) ^ 2 = 19 + 3 * y := by
            rw [Real.sq_sqrt] <;> linarith
        nlinarith
    have h₃ : y = 10 := by
        have h₃₁ : 19 + 3 * y = 49  := by
      
            gcongr
        have h₃₂ : y = 10 := by
            linarith
        exact h₃₂
    rw [h₃]
    <;> norm_num
    <;>
    linarith