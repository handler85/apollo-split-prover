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
theorem mathd_algebra_176 (x : ℝ) : (x + 1) ^ 2 * x = x ^ 3 + 2 * x ^ 2 + x := by
  have h_main : (x + 1) ^ 2 * x = x ^ 3 + 2 * x ^ 2 + x := by
    have h1 : (x + 1) ^ 2 = x ^ 2 + 2 * x + 1 := by
      ring
    rw [h1]
    ring
    <;>
    linarith
  exact h_main