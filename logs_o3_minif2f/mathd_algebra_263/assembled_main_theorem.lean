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
  have h2 : 19 + 3 * y = 7 * 7  := by
      linarith
  have h3 : 19 + 3 * y = 49  := by
      linarith
  have h4 : 3 * y = 49 - 19  := by
      linarith
  have h5 : 3 * y = 30  := by
      linarith
  have h6 : y = 10  := by
      try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith


      
      have h_main : y = 10 := by
        have h6 : y * 3 = 30 := h5
        have h7 : y = 10 := by
          -- Solve for y by dividing both sides by 3
          apply mul_left_cancel₀ (show (3 : ℝ) ≠ 0 by norm_num)
          nlinarith
        exact h7
      exact h_main


  exact h6