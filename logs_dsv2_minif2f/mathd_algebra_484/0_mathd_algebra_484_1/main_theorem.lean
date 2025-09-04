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

lemma mathd_algebra_484_1
  (h_main : Real.log (27 : ℝ) = (3 : ℝ) * Real.log (3 : ℝ)) :
  (0 : ℝ) < Real.log (3 : ℝ) := by
  have h_log_3_pos : (0 : ℝ) < Real.log (3 : ℝ) := by
    have h₁ : Real.log (3 : ℝ) > 0 := Real.log_pos (by norm_num)
    linarith
  exact h_log_3_pos
