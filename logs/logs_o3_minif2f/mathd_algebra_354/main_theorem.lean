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
theorem mathd_algebra_354 (a d : ℝ) (h₀ : a + 6 * d = 30) (h₁ : a + 10 * d = 60) :
    a + 20 * d = 135 := by
  have h_diff : (a + 10 * d) - (a + 6 * d) = 60 - 30 := by
    linarith
  have h_4d : 4 * d = 30 := by
    linarith
  have d_val : d = 15 / 2 := by
    linarith
  have a_val : a = 30 - 6 * d := by
    linarith
  have term21 : a + 20 * d = (30 - 6 * d) + 20 * d := by
    linarith
  have term21_simplified : a + 20 * d = 30 + 14 * d := by
    linarith
  have final_result : a + 20 * d = 135 := by
    linarith
  exact final_result