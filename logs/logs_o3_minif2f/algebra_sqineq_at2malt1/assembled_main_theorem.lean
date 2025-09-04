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
theorem algebra_sqineq_at2malt1 (a : ℝ) : a * (2 - a) ≤ 1 := by
  have h_expand : a * (2 - a) = 2 * a - a^2  := by
      linarith
  have h_rearrange : 1 - (2 * a - a^2) = a^2 - 2 * a + 1  := by
      linarith
  have h_factor : a^2 - 2 * a + 1 = (a - 1)^2  := by
      linarith
  have h_nonneg : (a - 1)^2 ≥ 0  := by
      exact sq_nonneg (a - (1 : ℝ))
  have h_final : a * (2 - a) ≤ 1  := by
      linarith
  exact h_final