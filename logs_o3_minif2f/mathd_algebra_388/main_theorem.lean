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
theorem mathd_algebra_388 (x y z : ℝ) 
  (h₀ : 3 * x + 4 * y - 12 * z = 10)
  (h₁ : -2 * x - 3 * y + 9 * z = -4) : x = 14 := by
  have h₀_mul : 9 * x + 12 * y - 36 * z = 30  := by
    linarith
  have h₁_mul : -8 * x - 12 * y + 36 * z = -16  := by
    linarith
  have h_sum : (9 * x + 12 * y - 36 * z) + (-8 * x - 12 * y + 36 * z) = 30 + (-16)  := by
    linarith
  have h_x : x = 14  := by
    linarith
  exact h_x