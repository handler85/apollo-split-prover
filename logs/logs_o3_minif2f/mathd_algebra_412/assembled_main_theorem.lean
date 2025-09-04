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
theorem mathd_algebra_412 (x y : ℝ) (h₀ : x + y = 25) (h₁ : x - y = 11) : x = 18 := by
  have h_add : (x + y) + (x - y) = 25 + 11 := by
    linarith
  have h_cancel : (x + y) + (x - y) = 2 * x := by
    linarith
  have h_twox : 2 * x = 36 := by
    linarith
  have h_div : x = 36 / 2 := by
    linarith
  have h_final : x = 18 := by
    linarith
  exact h_final