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

lemma mathd_algebra_263_1
  (y : ℝ)
  (h5 : y * (3 : ℝ) = (30 : ℝ))
  (h4 h2 : True) :
  y = (10 : ℝ) := by
  have h_main : y = 10 := by
    have h6 : y * 3 = 30 := h5
    have h7 : y = 10 := by
      -- Solve for y by dividing both sides by 3
      apply mul_left_cancel₀ (show (3 : ℝ) ≠ 0 by norm_num)
      nlinarith
    exact h7
  exact h_main
