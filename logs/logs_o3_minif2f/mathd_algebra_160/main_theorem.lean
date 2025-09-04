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
theorem mathd_algebra_160 (n x : ℝ) (h₀ : n + x = 97) (h₁ : n + 5 * x = 265) : n + 2 * x = 139 := by 
  have h_sub : (n + 5 * x) - (n + x) = 265 - 97  := by
    linarith
  have h_four_x : 4 * x = 168  := by
    linarith
  have x_val : x = 42  := by
    linarith
  have n_val : n = 97 - 42  := by
    linarith
  have two_hour_charge : n + 2 * x = (97 - 42) + 2 * 42  := by
    linarith
  have two_hour_charge_simplified : n + 2 * x = 139  := by
    linarith
  exact two_hour_charge_simplified