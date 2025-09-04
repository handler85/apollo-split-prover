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
theorem mathd_algebra_427 (x y z : ℝ) 
  (h₀ : 3 * x + y = 17) 
  (h₁ : 5 * y + z = 14)
  (h₂ : 3 * x + 5 * z = 41) : x + y + z = 12 := by
  have h_y : y = 17 - 3 * x  := by
    linarith
  have h_z_expr : z = 14 - 5 * (17 - 3 * x)  := by
    linarith
  have h_z : z = 15 * x - 71  := by
    linarith
  have h_x_eq : 3 * x + 5 * (15 * x - 71) = 41  := by
    linarith
  have h_x_val : x = 66 / 13  := by
    linarith
  have h_y_val : y = 17 - 3 * (66 / 13)  := by
    linarith
  have h_z_val : z = 15 * (66 / 13) - 71  := by
    linarith
  have sum_eq : x + y + z = (66 / 13) + (17 - 3 * (66 / 13)) + (15 * (66 / 13) - 71)  := by
    linarith
  exact try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  sorry
