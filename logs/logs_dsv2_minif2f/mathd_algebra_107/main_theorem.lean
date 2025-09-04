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
theorem mathd_algebra_107 (x y : ℝ) (h₀ : x ^ 2 + 8 * x + y ^ 2 - 6 * y = 0) :
    (x + 4) ^ 2 + (y - 3) ^ 2 = 5 ^ 2 := by
    have h₁ : (x + 4) ^ 2 + (y - 3) ^ 2 = 25 := by
        have h₁₀ : x ^ 2 + 8 * x + y ^ 2 - 6 * y = 0  := by
      
            gcongr
        have h₁₁ : (x + 4) ^ 2 + (y - 3) ^ 2 = 25 := by
            --nlinarith [sq_nonneg (x + 4 + (y - 3)), sq_nonneg (x + 4 - (y - 3))
                --sq_nonneg (x - y + 1), sq_nonneg (x + y - 1), sq_nonneg (x - y - 7)
        
            linarith
        exact h₁₁
    have h₂ : (x + 4) ^ 2 + (y - 3) ^ 2 = 5 ^ 2 := by
        have h₃ : (x + 4) ^ 2 + (y - 3) ^ 2 = 25  := by
      
            gcongr
        have h₄ : (5 : ℝ) ^ 2 = 25  := by
            norm_num
        nlinarith
    exact h₂