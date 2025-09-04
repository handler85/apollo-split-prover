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
theorem mathd_algebra_329 (x y : ℝ) (h₀ : 3 * y = x) (h₁ : 2 * x + 5 * y = 11) : x + y = 4 := by
  have h_substitution : 2 * (3 * y) + 5 * y = 11  := by
      linarith
  have h_simplify : 6 * y + 5 * y = 11  := by
      linarith
  have h_combine : 11 * y = 11  := by
      linarith
  have hy : y = 1  := by
      linarith
  have hx : x = 3  := by
      linarith
  have h_sum : x + y = 4  := by
      linarith
  exact h_sum